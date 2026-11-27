import WaringSiegel.WSL2MomentEighthGrowth
import WaringSiegel.WSL2MomentWeightedTransfer

/-!
# The first three genuine Hua moments over every number field

For cubic sums these are all the classical Hua exponents. The coefficients
may be arbitrary bounded complex numbers, and every integral uses the actual
probability Haar measure of the integral-coordinate torus.
-/

noncomputable section
open MeasureTheory
open scoped NumberField BigOperators Classical

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

theorem frequencySum_power_eq_image {α : Type*} [Fintype α]
    (nodes : α → 𝓞 K) (hinj : Function.Injective nodes) (k : ℕ)
    (θ : NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) :
    frequencySum (fun x => integerCoordinates K (nodes x ^ k)) (fun _ => 1) θ =
      finiteFrequencySum (Finset.univ.image nodes) (fun x => integerCoordinates K (x^k)) θ := by
  unfold frequencySum finiteFrequencySum
  simp only [one_mul]
  symm
  rw [Finset.sum_image]
  exact fun a ha b hb hab => hinj hab

/-- Weighted eighth moment with its genuine number-field Hua exponent. -/
theorem numberField_eighth_moment_bound (k : ℕ) (hk : 3 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^8 ∂latticeHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ) ^ (5 + ε) * W^8 := by
  obtain ⟨C, hC, hbound⟩ := numberField_eighth_moment_unweighted (K := K) k hk hε
  refine ⟨C, hC, ?_⟩
  intro P hP α inst nodes hinj hnodes w W hW hw
  have hu := hbound P hP (Finset.univ.image nodes) (by
    intro x hx v
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hnodes a v)
  have hu' : (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k))
      (fun _ => 1) θ‖^8 ∂latticeHaar) ≤ C * (P ^ Module.finrank ℚ K : ℝ)^(5+ε) := by
    simpa only [frequencySum_power_eq_image nodes hinj k] using hu
  change (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k)) w θ‖^8
    ∂latticeHaar) ≤ _
  calc
    _ ≤ W^8 * (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k))
        (fun _ => 1) θ‖^8 ∂latticeHaar) :=
      integral_norm_frequencySum_eighth_le_unweighted _ w W hW hw
    _ ≤ W^8 * (C * (P ^ Module.finrank ℚ K : ℝ)^(5+ε)) :=
      mul_le_mul_of_nonneg_left hu' (by positivity)
    _ = _ := by ring

/-- The second-moment member, expressed in the same volume scale as Hua. -/
theorem numberField_second_moment_bound (k : ℕ) (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^2 ∂latticeHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ) ^ (1 + ε) * W^2 := by
  let B : ℝ := 2 * (3 : ℝ)^Module.finrank ℚ K
  have hB : 0 < B := by dsimp [B]; positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨(k : ℝ)*B, mul_pos hkR hB, ?_⟩
  intro P hP α inst nodes hinj hnodes w W hW hw
  let X : ℝ := P^Module.finrank ℚ K
  have hX : 1 ≤ X := one_le_pow₀ hP
  have hXpow : X ≤ X^(1+ε) := by
    nth_rw 1 [← Real.rpow_one X]
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hN : (Fintype.card α : ℝ) ≤ B * X := by
    have h := integer_box_card_bound (Finset.univ.image nodes) P hP (by
      intro x hx v
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact hnodes a v)
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using h
  have hsum : (∑ a, ‖w a‖^2) ≤ (Fintype.card α : ℝ)*W^2 := by
    calc
      _ ≤ ∑ _a : α, W^2 := Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hw a) _)
      _ = _ := by simp
  calc
    (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^2 ∂latticeHaar) ≤
        (k : ℝ) * ∑ a, ‖w a‖^2 := numberField_monomial_second_moment_le K nodes hinj k hk w
    _ ≤ (k : ℝ)*((Fintype.card α : ℝ)*W^2) := mul_le_mul_of_nonneg_left hsum hkR.le
    _ ≤ (k : ℝ)*(B*X*W^2) := by gcongr
    _ ≤ (k : ℝ)*B*X^(1+ε)*W^2 := by
      have hm := mul_le_mul_of_nonneg_left hXpow (show 0 ≤ (k : ℝ)*B*W^2 by positivity)
      nlinarith only [hm]

/-- The actual first three Hua estimates, with exponents independent of the
degree of the field after passing to X=P^[K:Q]. -/
theorem numberField_low_hua_moments (k j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3)
    (hjk : j ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^(2^j) ∂latticeHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ) ^ ((2^j-j : ℕ) + ε) * W^(2^j) := by
  have hcases : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · simpa using numberField_second_moment_bound (K := K) k (by omega) hε
  · simpa using numberField_fourth_moment_bound (K := K) k hjk hε
  · simpa using numberField_eighth_moment_bound (K := K) k hjk hε

end WaringSiegel.WSL2
