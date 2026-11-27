import Waring.SeedCompletionWeylPowers
import Waring.SeedCompletionFamilyWeyl
import Waring.SeedCompletionNaturalBox
import Waring.FirstStageTransport
import Waring.SeedCompletionTerminalSecond

/-! # Exact ordinary differences into padded centered-phase boxes

All old height and coefficient coordinates are retained. The new
coefficient is one; the new height and center encode the difference and
sum of the two old centers. Even moments are enlarged only through the
proved finite equal-sum counts.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.SeedCompletionWeylTransport
open IntegerDifferencePolynomial PolicyCompletionMajorFamily
open SeedCompletionNaturalBox SeedCompletionBackwardMoments
open SeedCompletionBackwardCount SeedCompletionTerminalHolder
open PolicyCompletionHolder
open UnseparatedDifferencing QuadraticModulation
open SeedCompletionNinthFourthBounds (centers centers_pos centers_width centers_card
  sum_natural_centers)

def sourceLabels {j : ℕ} (H A : Fin j → Finset ℕ) : Finset (NaturalLabel j) :=
  Fintype.piFinset H ×ˢ Fintype.piFinset A

def sourceDomain {j : ℕ} (H A : Fin j → Finset ℕ) (N : ℕ) :=
  sourceLabels H A ×ˢ Finset.Icc 1 N

def sourceMoment {j : ℕ} (k : ℕ) (H A : Fin j → Finset ℕ) (N s : ℕ) : ℝ :=
  frequencyEvenMoment (sourceDomain H A N) (naturalPhase k) s

def phaseInt {j : ℕ} (k : ℕ) (b : NaturalLabel j) (z : ℤ) : ℤ :=
  (powerPolynomial k (naturalParameters b.1 b.2)).eval z

def positiveDomain {j : ℕ} (B : Finset (NaturalLabel j)) (Z : Finset ℤ) :=
  B ×ˢ positivePairs Z

def positivePhase {j : ℕ} (k : ℕ) (p : NaturalLabel j × (ℤ × ℤ)) : ℤ :=
  phaseInt k p.1 p.2.1-phaseInt k p.1 p.2.2

def differenceCode {j : ℕ} (p : NaturalLabel j × (ℤ × ℤ)) : NaturalLabel (j+1) × ℕ :=
  ((Fin.snoc (fun i => 2*p.1.1 i) (p.2.1-p.2.2).toNat,
    Fin.snoc p.1.2 1),(p.2.1+p.2.2).toNat)

def liftHeights {j : ℕ} (H : Fin j → Finset ℕ) (N : ℕ) : Fin (j+1) → Finset ℕ :=
  Fin.snoc (fun i => (H i).image (fun h => 2*h)) (Finset.Icc 1 N)

def liftCoefficients {j : ℕ} (A : Fin j → Finset ℕ) : Fin (j+1) → Finset ℕ :=
  Fin.snoc A {1}

theorem naturalParameters_snoc {j : ℕ} (h m : Fin j → ℕ) (t w : ℕ) :
    naturalParameters (Fin.snoc h t) (Fin.snoc m w)=
      naturalParameters h m ++ [((t:ℤ),(w:ℤ))] := by
  unfold naturalParameters
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append]

theorem naturalParameters_double {j : ℕ} (h m : Fin j → ℕ) :
    naturalParameters (fun i => 2*h i) m=doubleHeights (naturalParameters h m) := by
  simp [naturalParameters,doubleHeights,List.map_ofFn,Function.comp_def]

theorem differenceCode_injOn {j : ℕ} (B : Finset (NaturalLabel j)) (Z : Finset ℤ)
    (hZ : ∀ z ∈ Z, 1 ≤ z) : Set.InjOn (@differenceCode j) (positiveDomain B Z) := by
  intro x hx y hy he
  have hxp := Finset.mem_filter.mp (Finset.mem_product.mp hx).2
  have hyp := Finset.mem_filter.mp (Finset.mem_product.mp hy).2
  have hx1 := hZ x.2.1 (Finset.mem_product.mp hxp.1).1
  have hx2 := hZ x.2.2 (Finset.mem_product.mp hxp.1).2
  have hy1 := hZ y.2.1 (Finset.mem_product.mp hyp.1).1
  have hy2 := hZ y.2.2 (Finset.mem_product.mp hyp.1).2
  have hh : x.1.1=y.1.1 := by
    funext i
    have H := congrArg (fun p : NaturalLabel (j+1) × ℕ => p.1.1 i.castSucc) he
    simp only [differenceCode,Fin.snoc_castSucc] at H
    omega
  have hm : x.1.2=y.1.2 := by
    funext i
    simpa only [differenceCode,Fin.snoc_castSucc] using
      congrArg (fun p : NaturalLabel (j+1) × ℕ => p.1.2 i.castSucc) he
  have hd : (x.2.1-x.2.2).toNat=(y.2.1-y.2.2).toNat := by
    simpa only [differenceCode,Fin.snoc_last] using
      congrArg (fun p : NaturalLabel (j+1) × ℕ => p.1.1 (Fin.last j)) he
  have hs : (x.2.1+x.2.2).toNat=(y.2.1+y.2.2).toNat := congrArg Prod.snd he
  exact Prod.ext (Prod.ext hh hm) (Prod.ext (by omega) (by omega))

theorem differenceCode_phase {j : ℕ} (k : ℕ) (b : NaturalLabel j) (z z' : ℤ)
    (hm : ∀ i, 0 < b.2 i) (hz : 1 ≤ z) (hz' : 1 ≤ z') (horder : z' < z) :
    naturalPhase k (differenceCode (b,(z,z')))=(2 : ℤ)^k*positivePhase k (b,(z,z')) := by
  have hparams : ∀ p ∈ naturalParameters b.1 b.2,p.2≠0 := by
    simp only [naturalParameters,List.forall_mem_ofFn_iff]
    intro i
    exact_mod_cast (hm i).ne'
  have hdouble : ∀ p ∈ doubleHeights (naturalParameters b.1 b.2),p.2≠0 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hparams q hq
  have hperm := powerPolynomial_perm k
    (show (doubleHeights (naturalParameters b.1 b.2) ++ [(z-z',1)]).Perm
      ([(z-z',1)] ++ doubleHeights (naturalParameters b.1 b.2)) from List.perm_append_comm) (by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hdouble p hp
      · have hp' := List.mem_singleton.mp hp
        rw [hp']
        norm_num)
  simp only [naturalPhase,differenceCode,naturalParameters_snoc,naturalParameters_double,
    Nat.cast_one,Int.toNat_of_nonneg (by omega : 0 ≤ z-z'),
    Int.toNat_of_nonneg (by omega : 0 ≤ z+z')]
  rw [hperm]
  exact SeedCompletionFamilyWeyl.integer_backward_identity k _ hparams z z'

theorem differenceCode_mem {j : ℕ} (H A : Fin j → Finset ℕ) (N : ℕ)
    {p : NaturalLabel j × (ℤ × ℤ)} (hp : p∈positiveDomain (sourceLabels H A) (centers N)) :
    differenceCode p∈sourceDomain (liftHeights H N) (liftCoefficients A) (2*N) := by
  obtain ⟨hb,hp⟩ := Finset.mem_product.mp hp
  obtain ⟨hh,hm⟩ := Finset.mem_product.mp hb
  obtain ⟨hz,horder⟩ := Finset.mem_filter.mp hp
  obtain ⟨hz,hz'⟩ := Finset.mem_product.mp hz
  have hz := Finset.mem_Icc.mp hz
  have hz' := Finset.mem_Icc.mp hz'
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simp only [differenceCode,liftHeights,Fin.snoc_last,Finset.mem_Icc]
      omega
    · simp only [differenceCode,liftHeights,Fin.snoc_castSucc]
      exact Finset.mem_image.mpr ⟨p.1.1 l,Fintype.mem_piFinset.mp hh l,rfl⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simp [differenceCode,liftCoefficients]
    · simpa only [differenceCode,liftCoefficients,Fin.snoc_castSucc] using
        Fintype.mem_piFinset.mp hm l
  · simp only [differenceCode,Finset.mem_Icc]
    omega

theorem firstDifference_eq_frequencySum {j : ℕ} (k : ℕ)
    (B : Finset (NaturalLabel j)) (Z : Finset ℤ) (N : ℕ)
    (hwidth : ∀ z ∈ Z, ∀ w ∈ Z, z-w ≤ (N : ℤ)) (α : ℝ) :
    firstDifference B (fun _ => Z)
      (fun b z => fourier (phaseInt k b z) (α : AddCircle (1 : ℝ))) N =
      frequencySum (positiveDomain B Z) (positivePhase k) α := by
  rw [firstDifference_eq]
  unfold frequencySum positiveDomain
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← positive_pairs_eq_differences Z _ N hwidth]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← fourier_neg,← fourier_add]
  rfl

theorem sourceFamily_eq_frequencySum {j : ℕ} (k : ℕ)
    (H A : Fin j → Finset ℕ) (N : ℕ) (α : ℝ) :
    familySum (sourceLabels H A) (fun _ => centers N)
      (fun b z => fourier (phaseInt k b z) (α : AddCircle (1 : ℝ))) =
      frequencySum (sourceDomain H A N) (naturalPhase k) α := by
  unfold familySum frequencySum sourceDomain
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b hb
  exact (sum_natural_centers N (fun z =>
    fourier ((powerPolynomial k (naturalParameters b.1 b.2)).eval z) (α : AddCircle (1 : ℝ)))).symm

theorem difference_moment_le_source {j : ℕ} (k s : ℕ)
    (H A : Fin j → Finset ℕ) (N : ℕ) (hA : ∀ i, ∀ m∈A i, 0<m) :
    (∫ α in (0 : ℝ)..1,
      ‖firstDifference (sourceLabels H A) (fun _ => centers N)
        (fun b z => fourier (phaseInt k b z) (α : AddCircle (1 : ℝ))) N‖^(2*s)) ≤
      sourceMoment k (liftHeights H N) (liftCoefficients A) (2*N) s := by
  simp_rw [firstDifference_eq_frequencySum k _ _ N (centers_width N)]
  change frequencyEvenMoment _ (positivePhase k) s ≤ _
  rw [← frequencyEvenMoment_mul_frequency _ (positivePhase k) s ((2:ℤ)^k) (by positivity)]
  apply FirstStageTransport.frequencyEvenMoment_le_of_injOn _ _ differenceCode
    (differenceCode_injOn _ _ (fun _ hz => centers_pos hz)) (naturalPhase k)
  · intro p hp
    have hb := Finset.mem_product.mp (Finset.mem_product.mp hp).1
    have hz := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
    exact differenceCode_phase k p.1 p.2.1 p.2.2
      (fun i => hA i _ (Fintype.mem_piFinset.mp hb.2 i))
      (centers_pos (Finset.mem_product.mp hz.1).1)
      (centers_pos (Finset.mem_product.mp hz.1).2) hz.2
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact differenceCode_mem H A N hp

theorem source_moment_double {j : ℕ} (k r : ℕ)
    (H A : Fin j → Finset ℕ) (N : ℕ) (hA : ∀ i, ∀ m∈A i, 0<m) :
    sourceMoment k H A N (2*r) ≤
      (2*(N : ℝ)*((sourceLabels H A).card : ℝ)^2)^r*sourceMoment k H A N r+
      (4*((sourceLabels H A).card : ℝ))^(2*r)*
        sourceMoment k (liftHeights H N) (liftCoefficients A) (2*N) r := by
  have h := SeedCompletionWeylPowers.fourier_family_double_even_moment_bound
    (sourceLabels H A) (fun _ => centers N) (phaseInt k) N r
    (fun _ _ => (centers_card N).le) (fun _ _ => centers_width N)
  simp_rw [sourceFamily_eq_frequencySum] at h
  have hD := difference_moment_le_source k r H A N hA
  change (∫ α in (0 : ℝ)..1,
    ‖frequencySum (sourceDomain H A N) (naturalPhase k) α‖^(2*(2*r))) ≤ _
  rw [show 2*(2*r)=4*r by omega]
  apply h.trans
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left hD (by positivity)

theorem sourceMoment_one_eq_second {j : ℕ} (k : ℕ)
    (H A : Fin j → Finset ℕ) (N : ℕ) :
    sourceMoment k H A N 1=
      SeedCompletionTerminalSecond.sourceSecondMoment k
        (Fintype.piFinset H) (Fintype.piFinset A) (Finset.Icc 1 N) := by
  simp only [sourceMoment,frequencyEvenMoment,sourceDomain,sourceLabels,
    SeedCompletionTerminalSecond.sourceSecondMoment,Finset.sum_product,
    naturalPhase,SeedCompletionTerminalPhase.phase,Nat.mul_one]

#print axioms difference_moment_le_source
#print axioms source_moment_double
end Waring.SeedCompletionWeylTransport
