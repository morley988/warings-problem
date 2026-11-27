import WaringSiegel.WSL2MomentEighthCounting
import WaringSiegel.WSL2MomentFourthGrowth
import WaringSiegel.WSL2MomentDivisorGrowth

/-!
# Actual number-field eighth moments

The previous modules prove the analytic Cauchy reduction and the polynomial
fiber counts. Here all finite parameters receive their proved uniform
number-field bounds.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

theorem fourthPowerValue_norm_le (S : Finset (𝓞 K)) {P : ℝ} (hP : 0 ≤ P)
    (hS : ∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    (k : ℕ) (q : ((𝓞 K) × (𝓞 K)) × ((𝓞 K) × (𝓞 K)))
    (hq : q ∈ (S.product S).product (S.product S)) :
    absNorm (fourthPowerValue k q) ≤
      (4 : ℝ) ^ Module.finrank ℚ K * P ^ (k * Module.finrank ℚ K) := by
  obtain ⟨hql, hqr⟩ := Finset.mem_product.mp hq
  obtain ⟨h11, h12⟩ := Finset.mem_product.mp hql
  obtain ⟨h21, h22⟩ := Finset.mem_product.mp hqr
  have hbox (v : NumberField.InfinitePlace K) : v ((fourthPowerValue k q : 𝓞 K) : K) ≤ 4 * P ^ k := by
    have h := place_sub_le_twice
      (place_power_sub_le_twice hP (hS _ h11) (hS _ h12) k)
      (place_power_sub_le_twice hP (hS _ h21) (hS _ h22) k) v
    simpa only [fourthPowerValue, ← mul_assoc, show (2 : ℝ)*2=4 by norm_num] using h
  have h := absNorm_le_box (by positivity) hbox
  simpa only [mul_pow, ← pow_mul] using h

theorem additiveDifferences_place_bound (S : Finset (𝓞 K)) {P : ℝ}
    (hS : ∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    {h : 𝓞 K} (hh : h ∈ additiveDifferences S) (v : NumberField.InfinitePlace K) :
    v (h : K) ≤ 2 * P := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
  exact place_sub_le_twice (hS _ (Finset.mem_product.mp hp).1)
    (hS _ (Finset.mem_product.mp hp).2) v

theorem fourthPowerValue_divisors_rpow_bound (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ S : Finset (𝓞 K),
      (∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P) →
      ∀ q ∈ (S.product S).product (S.product S), fourthPowerValue k q ≠ 0 →
      (((additiveDifferences S).filter (fun h => h ≠ 0 ∧ h ∣ fourthPowerValue k q)).card : ℝ) ≤
        C * P ^ ε := by
  obtain ⟨C, hC, hbound⟩ := ring_divisor_polynomial_norm_rpow_bound
    (K := K) (k * Module.finrank ℚ K) ((4 : ℝ)^Module.finrank ℚ K) (by positivity) hε
  refine ⟨C, hC, ?_⟩
  intro P hP S hS q hq ha
  apply hbound P hP (fourthPowerValue k q) ha
    (fourthPowerValue_norm_le S (by linarith) hS k q hq)
  · intro h hh
    exact (Finset.mem_filter.mp hh).2.2
  · intro h hh v
    exact additiveDifferences_place_bound S hS (Finset.mem_filter.mp hh).1 v

theorem finiteFrequencySum_power_eq_subtype (S : Finset (𝓞 K)) (k : ℕ)
    (θ : NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) :
    finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ =
      finiteWeylSum (integerCoordinates K) k (fun x : S => (x : 𝓞 K)) (fun _ => 1) θ := by
  simp only [finiteFrequencySum, finiteWeylSum, one_mul]
  exact Finset.sum_subtype S (fun _ => Iff.rfl) _

/-- Hua's genuine eighth-moment exponent, for every k at least three and
every finite set of algebraic integers in the given archimedean box. -/
theorem numberField_eighth_moment_unweighted (k : ℕ) (hk : 3 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ S : Finset (𝓞 K),
      (∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P) →
      (∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^8 ∂latticeHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ) ^ (5 + ε) := by
  let d : ℕ := Module.finrank ℚ K
  have hd : (0 : ℝ) < d := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  let η : ℝ := (d : ℝ) * ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A, hA, hfourth⟩ := numberField_fourth_moment_bound (K := K) k (by omega) hε
  obtain ⟨B, hB, hdiv⟩ := fourthPowerValue_divisors_rpow_bound (K := K) k hη
  let CS : ℝ := 2 * (3 : ℝ)^d
  let CH : ℝ := CS * (2 : ℝ)^d
  let Z : ℝ := 2 * CH * CS + (k-2 : ℕ)*CH^2
  have hCS : 0 < CS := by dsimp [CS]; positivity
  have hCH : 0 < CH := by dsimp [CH]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let C : ℝ := CH * (A * Z + CS^4 * (k-2 : ℕ)*B^2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP S hS
  let X : ℝ := P^d
  let H := additiveDifferences S
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hX : 0 < X := by dsimp [X]; positivity
  have hN : (S.card : ℝ) ≤ CS * X := integer_box_card_bound S P hP hS
  have hH : (H.card : ℝ) ≤ CH * X := by
    have hh := integer_box_card_bound H (2*P) (by linarith) (by
      intro h hh v
      exact additiveDifferences_place_bound S hS hh v)
    rw [mul_pow] at hh
    convert hh using 1 <;> dsimp [CH, CS, X] <;> ring
  have hshift : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H :=
    fun _ hx _ hy => additiveDifferences_mem S hx hy
  have hI4 : (∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^4 ∂latticeHaar) ≤
      A * X^(2+ε) := by
    have h := hfourth P hP (fun x : S => (x : 𝓞 K)) Subtype.val_injective
      (fun x v => hS x x.property v) (fun _ => (1 : ℂ)) 1 (by norm_num) (by intro x; simp)
    simpa only [← finiteFrequencySum_power_eq_subtype, one_pow, mul_one] using h
  have hI4nonneg : 0 ≤
      (∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^4 ∂latticeHaar) :=
    integral_nonneg (fun _ => by positivity)
  have hZbound : 2*(H.card : ℝ)*S.card + (k-2 : ℕ)*(H.card : ℝ)^2 ≤ Z*X^2 := by
    calc
      _ ≤ 2*(CH*X)*(CS*X) + (k-2 : ℕ)*(CH*X)^2 := by gcongr
      _ = _ := by dsimp [Z]; ring
  have hDpower : (B * P^η)^2 = B^2 * X^ε := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (P^η) 2, ← Real.rpow_mul hPpos.le]
    dsimp [η, X]
    rw [← Real.rpow_natCast P d, ← Real.rpow_mul hPpos.le]
    congr 1
    ring
  have hpow₁ : X^(2+ε)*X^2 = X^(4+ε) := by
    rw [← Real.rpow_natCast X 2, ← Real.rpow_add hX]
    congr 1
    ring
  have hpow₂ : X^4*X^ε = X^(4+ε) := by
    rw [← Real.rpow_natCast X 4, ← Real.rpow_add hX]
    norm_num
  have hpow₃ : X*X^(4+ε) = X^(5+ε) := by
    nth_rw 1 [← Real.rpow_one X]
    rw [← Real.rpow_add hX]
    congr 1
    ring
  have hred := integral_eighth_le_fourth_and_divisors S H hshift
    (integerCoordinates K) (integerCoordinates_injective K) k hk (B*P^η)
    (hdiv P hP S hS)
  rw [hDpower] at hred
  calc
    (∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^8 ∂latticeHaar) ≤
        (H.card : ℝ) *
          ((∫ θ, ‖finiteFrequencySum S (fun x => integerCoordinates K (x^k)) θ‖^4 ∂latticeHaar) *
            (2*(H.card : ℝ)*S.card + (k-2 : ℕ)*(H.card : ℝ)^2) +
            (S.card : ℝ)^4 * (k-2 : ℕ)*(B^2*X^ε)) := hred
    _ ≤ (CH*X) * (A*X^(2+ε)*(Z*X^2) + (CS*X)^4*(k-2 : ℕ)*(B^2*X^ε)) := by
      gcongr
    _ = CH * (A*Z*(X^(2+ε)*X^2) + CS^4*(k-2 : ℕ)*B^2*(X^4*X^ε))*X := by ring
    _ = C * (X * X^(4+ε)) := by rw [hpow₁, hpow₂]; dsimp [C]; ring
    _ = C * X^(5+ε) := by rw [hpow₃]

end WaringSiegel.WSL2
