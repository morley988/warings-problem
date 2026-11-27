import Waring.AuxiliaryFrozen

/-!
# The actual smooth coefficient enlargement in the depth-six count

The coefficient upper range is P^phi_i * R, rather than just P^phi_i.
A common positive smoothness exponent eta is chosen after epsilon and the
fixed strict margins. All six extra eta contributions are absorbed into the
arbitrary final epsilon. The efficient-difference F6 integral estimate remains
a separate analytic input.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliarySmoothScales
open AuxiliaryCounting AuxiliaryScales AuxiliaryFrozen

theorem blockRange_mono {H M H' M' : ℕ} (hH : H ≤ H') (hM : M ≤ M') :
    blockRange H M ⊆ blockRange H' M' := by
  intro x hx
  rcases mem_blockRange.mp hx with ⟨hh,hm,hn⟩
  apply mem_blockRange.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hh).1,(Finset.mem_Icc.mp hh).2.trans hH⟩,
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,(Finset.mem_Icc.mp hm).2.trans hM⟩,
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hM⟩⟩

theorem extendFamily_mono {S T : Finset (List PowerDifferenceFibers.Block)}
    {B C : Finset PowerDifferenceFibers.Block} (hS : S ⊆ T) (hB : B ⊆ C) :
    extendFamily S B ⊆ extendFamily T C :=
  Finset.image_subset_image (Finset.product_subset_product hS hB)

theorem prefixFamily_mono (H M H' M' : ℕ → ℕ) (r : ℕ)
    (hH : ∀ i < r, H i ≤ H' i) (hM : ∀ i < r, M i ≤ M' i) :
    prefixFamily H M r ⊆ prefixFamily H' M' r := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih =>
    exact extendFamily_mono
      (ih (fun i hi => hH i (by omega)) (fun i hi => hM i (by omega)))
      (blockRange_mono (hH r (by omega)) (hM r (by omega)))

theorem zeroCount_mono (k : ℕ) {S T : Finset (List PowerDifferenceFibers.Block)} (hS : S ⊆ T) :
    zeroCount k S ≤ zeroCount k T :=
  Finset.card_le_card (Finset.filter_subset_filter _ hS)

/-- A fixed positive perturbation range, strictly smaller than all six margins. -/
theorem perturbed_prefix8 {η : ℝ} (hη : 0 ≤ η) (hηcap : η ≤ 1/100000000) :
    ∀ i < 6, (∑ j ∈ Finset.range i, (phi8 j+η)) < shiftExponent8 i+(phi8 i+η) := by
  intro i hi
  interval_cases i <;>
    norm_num [shiftExponent8,phi8,phi8Q,Finset.sum_range_succ] <;> nlinarith

theorem perturbed_diagonal8 (η : ℝ) :
    (∑ i ∈ Finset.range 6, (shiftExponent8 i+(phi8 i+η))) =
      (223249759/100000000 : ℝ)+6*η := by
  simp_rw [← add_assoc]
  rw [Finset.sum_add_distrib,diagonal_exponent8]
  simp

/-- The actual upper coefficient range M_i R with M_i=P^phi_i. -/
def smoothCoefficientScale (P R : ℝ) (i : ℕ) : ℕ := ⌊P^(phi8 i)*R⌋₊

theorem smoothCoefficientScale_le {P R η : ℝ} (hP : 0 < P) (hR : R ≤ P^η) (i : ℕ) :
    smoothCoefficientScale P R i ≤ floorScale P (phi8 i+η) := by
  apply Nat.floor_mono
  rw [Real.rpow_add hP]
  exact mul_le_mul_of_nonneg_left hR (by positivity)

/-- The genuine six-block coefficient count in the enlarged smooth ranges.
The same eta, C and lower cutoff work for every 1<=R<=P^eta. No analytic F6
moment theorem is assumed or concluded here. -/
theorem frozen_depth6_smooth_zeroCount {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      (zeroCount 16 (prefixFamily (fun i => floorScale P (shiftExponent8 i))
        (smoothCoefficientScale P R) 6) : ℝ) ≤
        C*P^((223249759/100000000 : ℝ)+ε) := by
  let η : ℝ := min (ε/12) (1/100000000)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηcap : η ≤ 1/100000000 := min_le_right _ _
  have hηε : 6*η ≤ ε/2 := by have := min_le_left (ε/12) (1/100000000 : ℝ); dsimp [η]; linarith
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := auxiliary_zeroCount_real_scales 16 6 (by norm_num)
    shiftExponent8 (fun i => phi8 i+η) (show (0 : ℝ) ≤ 3 by norm_num)
    (show 0 < ε/2 by positivity) shiftExponent8_pos
    (by intro i hi; exact add_pos_of_pos_of_nonneg (phi8_pos i hi) hη.le)
    (perturbed_prefix8 hη.le hηcap)
    (by intro i hi; norm_num only [Nat.cast_ofNat]; have := block_exponent8 i; nlinarith)
  refine ⟨η,hη,C,hC,P₀,hP₀,?_⟩
  intro P hP R hR hRP
  have hP1 : 1 ≤ P := hP₀.trans hP
  have hpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hmono := zeroCount_mono 16
    (prefixFamily_mono (fun i => floorScale P (shiftExponent8 i)) (smoothCoefficientScale P R)
      (fun i => floorScale P (shiftExponent8 i)) (fun i => floorScale P (phi8 i+η)) 6
      (by intro i hi; exact le_rfl) (fun i hi => smoothCoefficientScale_le hpos hRP i))
  have hb := hbound P hP
  rw [perturbed_diagonal8] at hb
  calc
    _ ≤ (zeroCount 16 (prefixFamily (fun i => floorScale P (shiftExponent8 i))
        (fun i => floorScale P (phi8 i+η)) 6) : ℝ) := by exact_mod_cast hmono
    _ ≤ C*P^((223249759/100000000 : ℝ)+6*η+ε/2) := hb
    _ ≤ C*P^((223249759/100000000 : ℝ)+ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)) hC.le

#print axioms frozen_depth6_smooth_zeroCount
end Waring.AuxiliarySmoothScales
