import WaringSiegel.WSL2MomentProductCompression
import WaringSiegel.WSL2MomentEighthGrowth

/-!
# Uniform divisor compression of the actual cubic Weyl kernel

The final finite bound assumes only an archimedean box for the original
nodes. All product multiplicities are controlled by proved ideal and unit
counts, with arbitrary small power loss.
-/

noncomputable section
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

theorem shiftProducts_norm_le (H : Finset (𝓞 K)) {P : ℝ} (hP : 0 ≤ P)
    (hH : ∀ h ∈ H, ∀ v : NumberField.InfinitePlace K, v (h : K) ≤ 2*P)
    {a : 𝓞 K} (ha : a ∈ shiftProducts H) :
    absNorm a ≤ (4 : ℝ)^Module.finrank ℚ K * P^(2*Module.finrank ℚ K) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  have hbox (v : NumberField.InfinitePlace K) : v ((p.1*p.2 : 𝓞 K) : K) ≤ 4*P^2 := by
    change v ((p.1 : K)*(p.2 : K)) ≤ 4*P^2
    rw [map_mul]
    have h := mul_le_mul (hH _ (Finset.mem_product.mp hp).1 v)
      (hH _ (Finset.mem_product.mp hp).2 v) (apply_nonneg v _) (by positivity)
    nlinarith only [h]
  have h := absNorm_le_box (by positivity) hbox
  simpa only [mul_pow, ← pow_mul] using h

theorem shiftProductDivisors_rpow_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H : Finset (𝓞 K),
      (∀ h ∈ H, ∀ v : NumberField.InfinitePlace K, v (h : K) ≤ 2*P) →
      ∀ a ∈ shiftProducts H, a ≠ 0 →
      ((H.filter (fun h => h ≠ 0 ∧ h ∣ a)).card : ℝ) ≤ C*P^ε := by
  obtain ⟨C, hC, hbound⟩ := ring_divisor_polynomial_norm_rpow_bound (K := K)
    (2*Module.finrank ℚ K) ((4 : ℝ)^Module.finrank ℚ K) (by positivity) hε
  refine ⟨C, hC, ?_⟩
  intro P hP H hH a ha ha0
  apply hbound P hP a ha0 (shiftProducts_norm_le H (by linarith) hH ha)
  · intro h hh
    exact (Finset.mem_filter.mp hh).2.2
  · intro h hh v
    exact hH h (Finset.mem_filter.mp hh).1 v

/-- Actual double-shift sums admit epsilon product compression over O_K. -/
theorem numberField_product_kernel_rpow_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H : Finset (𝓞 K),
      (∀ h ∈ H, ∀ v : NumberField.InfinitePlace K, v (h : K) ≤ 2*P) →
      ∀ F : 𝓞 K → ℝ, (∀ a, 0 ≤ F a) →
      (∑ h ∈ H, ∑ j ∈ H, F (h*j)) ≤
        2*(H.card : ℝ)*F 0 + C*P^ε*∑ a ∈ (shiftProducts H).filter (fun a => a ≠ 0), F a := by
  obtain ⟨C, hC, hbound⟩ := shiftProductDivisors_rpow_bound (K := K) hε
  exact ⟨C, hC, fun P hP H hH F hF =>
    product_kernel_sum_le H F hF (C*P^ε) (hbound P hP H hH)⟩

/-- Concrete number-field cubic Weyl inequality after genuine divisor
compression. The lower cubic coefficients remain completely arbitrary. -/
theorem numberField_cubic_box_compressed_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ lo hi : NumberFieldCoordinateIndex K → ℤ,
      (∀ x ∈ coordinateLatticeBox (integerCoordinateAddEquiv K) lo hi,
        ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P) →
      ∀ a b c d : 𝓞 K, ∀ θ : NumberFieldCoordinateIndex K → AddCircle (1 : ℝ),
      let S := coordinateLatticeBox (integerCoordinateAddEquiv K) lo hi
      let H := additiveDifferences S
      ‖finitePolynomialSum S (integerCoordinates K) (cubicPolynomial a b c d)
        (fun _ => 1) θ‖^4 ≤
        2*(H.card : ℝ)^2*S.card + C*(H.card : ℝ)*(P^Module.finrank ℚ K : ℝ)^ε *
          ∑ z ∈ (shiftProducts H).filter (fun z => z ≠ 0),
            cubicBoxKernel (integerCoordinateAddEquiv K) (integerCoordinates K) a lo hi θ z := by
  have hd : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  obtain ⟨C, hC, hbound⟩ := numberField_product_kernel_rpow_bound (K := K)
    (show 0 < (Module.finrank ℚ K : ℝ)*ε from mul_pos hd hε)
  refine ⟨C, hC, ?_⟩
  intro P hP lo hi hS a b c d θ
  dsimp
  let S := coordinateLatticeBox (integerCoordinateAddEquiv K) lo hi
  let H := additiveDifferences S
  let F := cubicBoxKernel (integerCoordinateAddEquiv K) (integerCoordinates K) a lo hi θ
  have hsum := hbound P hP H
    (fun h hh v => additiveDifferences_place_bound S hS hh v) F
    (fun z => cubicBoxKernel_nonneg _ _ _ _ _ _ z)
  have hzero : F 0 = (S.card : ℝ) := cubicBoxKernel_zero _ _ _ _ _ _
  have hp : P^((Module.finrank ℚ K : ℝ)*ε) = (P^Module.finrank ℚ K : ℝ)^ε := by
    rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
  rw [hzero, hp] at hsum
  have hpoint := numberField_cubic_box_fourth_bound K lo hi a b c d θ
  have hmul := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ H.card by positivity)
  apply hpoint.trans
  convert hmul using 1 <;> ring

end WaringSiegel.WSL2
