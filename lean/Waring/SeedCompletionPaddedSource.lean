import Waring.SeedCompletionWeylTransport
import Waring.SeedCompletionNaturalScales
import Waring.SeedCompletionTerminalBox

/-! # Literal source boxes with fixed-one ordinary-difference slots -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionPaddedSource
open SeedCompletionWeylTransport SeedCompletionNaturalBox
open PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges CartesianProductSampling
open SeedCompletionSourceBounds SeedCompletionTerminalSparse CoefficientPower

def rangeSet (L : ℝ) : Finset ℕ := Finset.Icc 1 ⌊L⌋₊

def originalHeights {j : ℕ} (k : ℕ) (L : ℝ) (M : Fin j → ℝ) : Fin j → Finset ℕ :=
  fun i => rangeSet (boxHeights k L M i)

def originalCoefficients {j : ℕ} (P R : ℝ) (M : Fin j → ℝ) : Fin j → Finset ℕ :=
  fun i => coefficientBlock P R (M i)

def paddedHeights {j : ℕ} (k r : ℕ) (L : ℝ) (M : Fin j → ℝ) : Fin (j+r) → Finset ℕ :=
  Fin.append (originalHeights k L M) (fun _ => rangeSet L)

def paddedCoefficients {j : ℕ} (r : ℕ) (P R : ℝ) (M : Fin j → ℝ) : Fin (j+r) → Finset ℕ :=
  Fin.append (originalCoefficients P R M) (fun _ => {1})

def paddedMoment {j : ℕ} (k r s : ℕ) (D : ℝ) (φ : Fin j → ℝ) (P R : ℝ) : ℝ :=
  sourceMoment k (paddedHeights k r (D*P) (fun i => P^(φ i)))
    (paddedCoefficients r P R (fun i => P^(φ i))) ⌊D*P⌋₊ s

def paddedCard {j : ℕ} (k r : ℕ) (D : ℝ) (φ : Fin j → ℝ) (P R : ℝ) : ℝ :=
  ((sourceLabels (paddedHeights k r (D*P) (fun i => P^(φ i)))
    (paddedCoefficients r P R (fun i => P^(φ i)))).card : ℝ)

theorem paddedMoment_nonneg {j : ℕ} (k r s : ℕ) (D : ℝ) (φ : Fin j → ℝ) (P R : ℝ) :
    0 ≤ paddedMoment k r s D φ P R := by
  unfold paddedMoment sourceMoment
  rw [frequencyEvenMoment_eq_card]
  positivity

@[simp] theorem rangeSet_card (L : ℝ) : (rangeSet L).card=⌊L⌋₊ := by
  simp [rangeSet,Nat.card_Icc]

theorem rangeSet_card_le {L : ℝ} (hL : 0≤L) : ((rangeSet L).card : ℝ)≤L := by
  rw [rangeSet_card]
  exact Nat.floor_le hL

theorem rangeSet_mono {L T : ℝ} (hLT : L≤T) : rangeSet L⊆rangeSet T := by
  intro n hn
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
    (Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono hLT)⟩

theorem double_rangeSet_subset {L : ℝ} (hL : 0≤L) :
    (rangeSet L).image (fun h=>2*h)⊆rangeSet (2*L) := by
  intro n hn
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hn
  have hh := Finset.mem_Icc.mp hh
  refine Finset.mem_Icc.mpr ⟨by omega,?_⟩
  apply Nat.le_floor
  have hhr : (h:ℝ)≤L := (by exact_mod_cast hh.2 : (h:ℝ)≤⌊L⌋₊).trans (Nat.floor_le hL)
  push_cast
  linarith

theorem snoc_constant {n : ℕ} {α : Type*} (a : α) :
    Fin.snoc (fun _ : Fin n=>a) a=(fun _=>a) := by
  funext i
  refine Fin.lastCases ?_ (fun l=>?_) i <;> simp

theorem paddedCoefficients_lift {j : ℕ} (r : ℕ) (P R : ℝ) (M : Fin j→ℝ) :
    liftCoefficients (paddedCoefficients r P R M)=paddedCoefficients (r+1) P R M := by
  unfold liftCoefficients paddedCoefficients
  rw [← Fin.append_snoc,snoc_constant]

theorem paddedHeights_snoc {j : ℕ} (k r : ℕ) (L : ℝ) (M : Fin j→ℝ) :
    paddedHeights k (r+1) L M=Fin.snoc (paddedHeights k r L M) (rangeSet L) := by
  unfold paddedHeights
  rw [← Fin.append_snoc,snoc_constant]

theorem paddedHeights_double_subset {j : ℕ} (k r : ℕ) {L : ℝ} (M : Fin j→ℝ)
    (hL : 0≤L) (hM : ∀ i,0<M i) (i : Fin (j+r)) :
    ((paddedHeights k r L M) i).image (fun h=>2*h)⊆(paddedHeights k r (2*L) M) i := by
  refine Fin.addCases (fun l=>?_) (fun l=>?_) i
  · simp only [paddedHeights,Fin.append_left,originalHeights]
    have he : boxHeights k (2*L) M l=2*boxHeights k L M l := by unfold boxHeights; ring
    rw [he]
    exact double_rangeSet_subset (div_nonneg hL (pow_nonneg (hM l).le _))
  · simp only [paddedHeights,Fin.append_right]
    exact double_rangeSet_subset hL

theorem paddedHeights_lift_subset {j : ℕ} (k r : ℕ) {L : ℝ} (M : Fin j→ℝ)
    (hL : 0≤L) (hM : ∀ i,0<M i) (i : Fin (j+r+1)) :
    (liftHeights (paddedHeights k r L M) ⌊L⌋₊) i⊆
      (paddedHeights k (r+1) (2*L) M) i := by
  rw [paddedHeights_snoc]
  refine Fin.lastCases ?_ (fun l=>?_) i
  · simpa [liftHeights,Fin.snoc,Fin.last,rangeSet] using
      rangeSet_mono (show L≤2*L by linarith)
  · simp only [liftHeights,Fin.snoc_castSucc]
    exact paddedHeights_double_subset k r M hL hM l

theorem sourceMoment_mono {j : ℕ} (k s : ℕ) {H A H' A' : Fin j→Finset ℕ}
    {N N' : ℕ} (hH : ∀ i,H i⊆H' i) (hA : ∀ i,A i⊆A' i) (hN : N≤N') :
    sourceMoment k H A N s≤sourceMoment k H' A' N' s := by
  apply frequencyEvenMoment_mono
  intro p hp
  obtain ⟨hb,hz⟩ := Finset.mem_product.mp hp
  obtain ⟨hh,hm⟩ := Finset.mem_product.mp hb
  refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
  · exact Fintype.mem_piFinset.mpr (fun i=>hH i (Fintype.mem_piFinset.mp hh i))
  · exact Fintype.mem_piFinset.mpr (fun i=>hA i (Fintype.mem_piFinset.mp hm i))
  · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hz).1,(Finset.mem_Icc.mp hz).2.trans hN⟩

theorem doubled_floor_le {L : ℝ} (hL : 0≤L) : 2*⌊L⌋₊≤⌊2*L⌋₊ := by
  apply Nat.le_floor
  push_cast
  exact mul_le_mul_of_nonneg_left (Nat.floor_le hL) (by norm_num)

theorem paddedCoefficients_pos {j : ℕ} (r : ℕ) (P R : ℝ) (M : Fin j→ℝ)
    (i : Fin (j+r)) : ∀ m∈paddedCoefficients r P R M i,0<m := by
  refine Fin.addCases (fun l=>?_) (fun l=>?_) i
  · intro m hm
    simp only [paddedCoefficients,Fin.append_left,originalCoefficients] at hm
    exact (SmoothMoments.mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1
  · simp only [paddedCoefficients,Fin.append_right,Finset.mem_singleton]
    intro m hm
    simpa only [hm] using Nat.zero_lt_one

theorem padded_moment_double {j : ℕ} (k r s : ℕ) {D P R : ℝ}
    (φ : Fin j→ℝ) (hD : 0<D) (hP : 0<P) :
    paddedMoment k r (2*s) D φ P R≤
      (2*(⌊D*P⌋₊ : ℝ)*(paddedCard k r D φ P R)^2)^s*paddedMoment k r s D φ P R+
      (4*paddedCard k r D φ P R)^(2*s)*paddedMoment k (r+1) s (2*D) φ P R := by
  have hM (i : Fin j) : 0<P^(φ i) := Real.rpow_pos_of_pos hP _
  have hL : 0≤D*P := (mul_pos hD hP).le
  have H := source_moment_double k s
    (paddedHeights k r (D*P) (fun i=>P^(φ i)))
    (paddedCoefficients r P R (fun i=>P^(φ i))) ⌊D*P⌋₊
    (paddedCoefficients_pos r P R _)
  apply H.trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [paddedCoefficients_lift]
  apply sourceMoment_mono
  · intro i
    simpa only [mul_assoc] using paddedHeights_lift_subset k r _ hL hM i
  · intro i
    exact Finset.Subset.refl _
  · simpa only [mul_assoc] using doubled_floor_le hL

theorem paddedCard_eq {j : ℕ} (k r : ℕ) (D : ℝ) (φ : Fin j→ℝ) (P R : ℝ) :
    paddedCard k r D φ P R=powerBoxCard k D φ P R*(⌊D*P⌋₊ : ℝ)^r := by
  simp [paddedCard,sourceLabels,paddedHeights,paddedCoefficients,originalHeights,
    originalCoefficients,rangeSet,powerBoxCard,naturalBoxLabels,positiveBox,
    boxHeightBounds,boxCoefficientTuples,Finset.card_product,Fintype.card_piFinset,
    Fin.prod_univ_add,Nat.card_Icc,Nat.cast_mul,Nat.cast_prod]
  ring

theorem paddedCard_power {k j : ℕ} (r : ℕ) {D : ℝ} (hD : 1≤D) (φ : Fin j→ℝ)
    (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedCard k r D φ) (parameterExponent k φ+(r:ℝ)) := by
  have hN : SourcePowerBound (fun P _=>(⌊D*P⌋₊ : ℝ)) 1 := by
    have H := powerCentersCard_power hD
    simpa [naturalCenters,Int.card_Icc] using H
  have H := (powerBoxCard_power hD φ hφ hshift).mul (hN.natPow r)
  norm_num only [one_mul] at H
  exact H.congr (fun P R _ _=>(paddedCard_eq k r D φ P R).symm)

#print axioms padded_moment_double
#print axioms paddedCard_power
end Waring.SeedCompletionPaddedSource
