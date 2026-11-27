import Waring.AuxiliarySmoothScales
import Waring.AuxiliaryTupleCount

/-!
# Source normalization of the frozen six-block coefficient count

VW95 defines P_j=2^j P and H_i=P_i M_i^(-k), hence the depth-six upper
shift range 2^(6-i)H_i equals 64 P^(1-8phi_i). The fixed factor 64 is absorbed
only after choosing a positive perturbation and a sufficiently large cutoff.
The actual M_i R coefficient upper ranges and their shared smoothness choice
are retained.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace Waring.AuxiliarySourceCount
open AuxiliaryCounting AuxiliaryScales AuxiliaryFrozen AuxiliarySmoothScales AuxiliaryTupleCount

def sourceEta (ε : ℝ) : ℝ := min (ε/24) (1/100000000)
def sourceShiftScale (P : ℝ) (i : ℕ) : ℕ := ⌊64*P^(shiftExponent8 i)⌋₊

theorem sourceEta_pos {ε : ℝ} (hε : 0 < ε) : 0 < sourceEta ε :=
  lt_min (by positivity) (by norm_num)

theorem sourceEta_le (ε : ℝ) : sourceEta ε ≤ 1/100000000 := min_le_right _ _

theorem twice_perturbed_prefix8 {η : ℝ} (hη : 0 ≤ η) (hηcap : η ≤ 1/100000000) :
    ∀ i < 6, (∑ j ∈ Finset.range i, (phi8 j+η)) < (shiftExponent8 i+η)+(phi8 i+η) := by
  intro i hi
  interval_cases i <;>
    norm_num [shiftExponent8,phi8,phi8Q,Finset.sum_range_succ] <;> nlinarith

theorem twice_perturbed_diagonal8 (η : ℝ) :
    (∑ i ∈ Finset.range 6, ((shiftExponent8 i+η)+(phi8 i+η))) =
      (223249759/100000000 : ℝ)+12*η := by
  have hp (i : ℕ) : (shiftExponent8 i+η)+(phi8 i+η)=(shiftExponent8 i+phi8 i)+2*η := by ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib,diagonal_exponent8]
  simp
  ring

theorem sourceShiftScale_le {P η : ℝ} (hP : 0 < P) (hlarge : 64 ≤ P^η) (i : ℕ) :
    sourceShiftScale P i ≤ floorScale P (shiftExponent8 i+η) := by
  apply Nat.floor_mono
  rw [Real.rpow_add hP]
  calc
    64*P^(shiftExponent8 i) ≤ P^η*P^(shiftExponent8 i) :=
      mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = _ := mul_comm _ _

/-- Genuine coefficient zero-count bound with the exact source shift constants. -/
theorem frozen_source_zeroCount {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R : ℝ, 1 ≤ R → R ≤ P^(sourceEta ε) →
      (zeroCount 16 (prefixFamily (sourceShiftScale P) (smoothCoefficientScale P R) 6) : ℝ) ≤
        C*P^((223249759/100000000 : ℝ)+ε) := by
  let η := sourceEta ε
  have hη : 0 < η := sourceEta_pos hε
  have hηcap : η ≤ 1/100000000 := sourceEta_le ε
  have hηε : 12*η ≤ ε/2 := by
    have h := min_le_left (ε/24) (1/100000000 : ℝ)
    change η ≤ ε/24 at h
    linarith
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := auxiliary_zeroCount_real_scales 16 6 (by norm_num)
    (fun i => shiftExponent8 i+η) (fun i => phi8 i+η) (show (0 : ℝ) ≤ 3 by norm_num)
    (show 0 < ε/2 by positivity)
    (by intro i hi; exact add_pos_of_pos_of_nonneg (shiftExponent8_pos i hi) hη.le)
    (by intro i hi; exact add_pos_of_pos_of_nonneg (phi8_pos i hi) hη.le)
    (twice_perturbed_prefix8 hη.le hηcap)
    (by intro i hi; norm_num only [Nat.cast_ofNat]; have := block_exponent8 i; nlinarith)
  obtain ⟨P₁,hP₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64 : ℝ)))
  refine ⟨C,hC,max P₀ P₁,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP R hR hRP
  have hP0 : P₀ ≤ P := (le_max_left _ _).trans hP
  have hP1 : 1 ≤ P := hP₀.trans hP0
  have hpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hlarge : 64 ≤ P^η := hP₁ P ((le_max_right _ _).trans hP)
  have hmono := zeroCount_mono 16
    (prefixFamily_mono (sourceShiftScale P) (smoothCoefficientScale P R)
      (fun i => floorScale P (shiftExponent8 i+η)) (fun i => floorScale P (phi8 i+η)) 6
      (fun i hi => sourceShiftScale_le hpos hlarge i)
      (fun i hi => smoothCoefficientScale_le hpos hRP i))
  have hb := hbound P hP0
  rw [twice_perturbed_diagonal8] at hb
  calc
    _ ≤ (zeroCount 16 (prefixFamily (fun i => floorScale P (shiftExponent8 i+η))
        (fun i => floorScale P (phi8 i+η)) 6) : ℝ) := by exact_mod_cast hmono
    _ ≤ C*P^((223249759/100000000 : ℝ)+12*η+ε/2) := hb
    _ ≤ C*P^((223249759/100000000 : ℝ)+ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)) hC.le

theorem coordinateBox_card (H : ℕ → ℕ) (r : ℕ) :
    (coordinateBox H r).card = ∏ i ∈ Finset.range r, H i := by
  simp [coordinateBox,Fintype.card_piFinset,Fin.prod_univ_eq_prod_range]

theorem shiftExponent8_le_one : ∀ i < 6, shiftExponent8 i ≤ 1 := by
  intro i hi
  have hp := phi8_pos i hi
  unfold shiftExponent8
  linarith

theorem phi8_perturbed_le_one {η : ℝ} (hηcap : η ≤ 1/100000000) :
    ∀ i < 6, phi8 i+η ≤ 1 := by
  intro i hi
  interval_cases i <;> norm_num [phi8,phi8Q] <;> linarith

theorem sourceShiftScale_real_le {P : ℝ} (hP : 1 ≤ P) {i : ℕ} (hi : i < 6) :
    (sourceShiftScale P i : ℝ) ≤ 64*P := by
  calc
    _ ≤ 64*P^(shiftExponent8 i) := Nat.floor_le (by positivity)
    _ ≤ 64*P^(1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (shiftExponent8_le_one i hi)) (by norm_num)
    _ = _ := by rw [Real.rpow_one]

theorem smoothCoefficientScale_real_le {P R η : ℝ} (hP : 1 ≤ P)
    (hηcap : η ≤ 1/100000000) (hRP : R ≤ P^η) {i : ℕ} (hi : i < 6) :
    (smoothCoefficientScale P R i : ℝ) ≤ P := by
  have hp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  calc
    _ ≤ (floorScale P (phi8 i+η) : ℝ) := by exact_mod_cast smoothCoefficientScale_le hp hRP i
    _ ≤ P^(phi8 i+η) := Nat.floor_le (by positivity)
    _ ≤ P^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (phi8_perturbed_le_one hηcap i hi)
    _ = P := Real.rpow_one P

/-- The number of coefficient m-tuples is at most P, including the R factors. -/
theorem smooth_coefficient_tuple_card_le {P R η : ℝ} (hP : 1 ≤ P)
    (hηcap : η ≤ 1/100000000) (hRP : R ≤ P^η) :
    ((coordinateBox (smoothCoefficientScale P R) 6).card : ℝ) ≤ P := by
  have hp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hsum : (∑ i ∈ Finset.range 6, (phi8 i+η)) =
      (53821463/100000000 : ℝ)+6*η := by
    norm_num [phi8,phi8Q,Finset.sum_range_succ]
    ring
  rw [coordinateBox_card,Nat.cast_prod]
  calc
    _ ≤ ∏ i ∈ Finset.range 6, P^(phi8 i+η) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
      intro i hi
      exact le_trans (by exact_mod_cast smoothCoefficientScale_le hp hRP i) (Nat.floor_le (by positivity))
    _ = P^(∑ i ∈ Finset.range 6, (phi8 i+η)) := (Real.rpow_sum_of_pos hp _ _).symm
    _ ≤ P^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by rw [hsum]; linarith)
    _ = P := Real.rpow_one P

#print axioms frozen_source_zeroCount
#print axioms smooth_coefficient_tuple_card_le
end Waring.AuxiliarySourceCount
