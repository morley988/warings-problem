import WaringSiegel.WSL2MomentDivisorBridge
import WaringSiegel.WSL2UnitLogGrowth
import WaringSiegel.WSL2IntegerBox

/-!
# Epsilon growth in the actual number-field fourth moment

All frequencies, sums, Haar integrals and divisor sets below are literal.
The only parameters left are the number field, the exponent, the box radius,
and a bound on the actual coefficients.
-/

noncomputable section
open MeasureTheory
open scoped NumberField BigOperators Classical

namespace WaringSiegel.WSL2

theorem nodeDivisorMaximum_cast_le {R α : Type*} [CommRing R]
    [IsDomain R] [CharZero R] [Fintype α] (nodes : α → R) (k : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ p : α × α, nodes p.1 ^ k - nodes p.2 ^ k ≠ 0 →
      ((powerDifferenceDivisors (Finset.univ.image nodes)
        (nodes p.1 ^ k - nodes p.2 ^ k)).card : ℝ) ≤ B) :
    (nodeDivisorMaximum nodes k : ℝ) ≤ B := by
  unfold nodeDivisorMaximum
  by_cases h : (Finset.univ : Finset (α × α)).Nonempty
  · obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup Finset.univ h
      (fun p : α × α => if nodes p.1 ^ k - nodes p.2 ^ k = 0 then 0 else
        (powerDifferenceDivisors (Finset.univ.image nodes)
          (nodes p.1 ^ k - nodes p.2 ^ k)).card)
    rw [heq]
    split_ifs with hz
    · simpa using hB
    · exact hb p hz
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty]
    simpa using hB

variable {K : Type*} [Field K] [NumberField K]

theorem nodeDivisorMaximum_log_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K,
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) → ∀ k : ℕ,
      (nodeDivisorMaximum nodes k : ℝ) ≤
        C * ((2 * P ^ k) ^ Module.finrank ℚ K : ℝ) ^ ε *
          (1 + Real.log (2 * P)) ^ NumberField.Units.rank K := by
  obtain ⟨C, hC, hbound⟩ := powerDifferenceDivisors_card_bound (K := K) hε
  refine ⟨C, hC, ?_⟩
  intro P hP α inst nodes hnodes k
  have hP0 : 0 ≤ P := by linarith
  have hlog : 0 ≤ 1 + Real.log (2 * P) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * P by linarith)]
  apply nodeDivisorMaximum_cast_le nodes k _ (by positivity)
  intro p hp
  apply hbound P hP (Finset.univ.image nodes)
  · intro x hx v
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hnodes a v
  · exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, rfl⟩
  · exact hp

/-- Every positive power absorbs the actual divisor maximum, uniformly in the nodes. -/
theorem nodeDivisorMaximum_rpow_bound (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K,
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      (nodeDivisorMaximum nodes k : ℝ) ≤ C * P ^ ε := by
  let d : ℕ := Module.finrank ℚ K
  have hd : 0 < d := Module.finrank_pos (R := ℚ) (M := K)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let δ : ℝ := ε / (2 * (k : ℝ) * (d : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, hdiv⟩ := nodeDivisorMaximum_log_bound (K := K) hδ
  obtain ⟨B, hB, hlog⟩ := exists_one_add_log_pow_le_rpow
    (NumberField.Units.rank K) (show 0 < ε / 2 by linarith)
  let C : ℝ := A * B * (2 : ℝ)^((d : ℝ) * δ) * (2 : ℝ)^(ε / 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP α inst nodes hnodes
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hn : ((2 * P ^ k) ^ d : ℝ) ^ δ =
      (2 : ℝ)^((d : ℝ)*δ) * P^((k : ℝ)*(d : ℝ)*δ) := by
    rw [← Real.rpow_natCast (2 * P ^ k) d,
      ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast P k, ← Real.rpow_mul hPpos.le]
    congr 2
    ring
  have he : (k : ℝ) * (d : ℝ) * δ + ε / 2 = ε := by
    dsimp [δ]
    field_simp
    ring
  calc
    (nodeDivisorMaximum nodes k : ℝ) ≤
        A * ((2 * P ^ k) ^ d : ℝ) ^ δ *
          (1 + Real.log (2 * P)) ^ NumberField.Units.rank K :=
      hdiv P hP nodes hnodes k
    _ ≤ A * ((2 * P ^ k) ^ d : ℝ) ^ δ * (B * (2 * P)^(ε / 2)) :=
      mul_le_mul_of_nonneg_left (hlog (2 * P) (by linarith)) (by positivity)
    _ = C * (P^((k : ℝ)*(d : ℝ)*δ) * P^(ε / 2)) := by
      rw [hn, Real.mul_rpow (by norm_num) hPpos.le]
      dsimp [C]
      ring
    _ = C * P ^ ε := by rw [← Real.rpow_add hPpos, he]

/-- The proved fourth moment with its exact cardinal-square and epsilon loss. -/
theorem numberField_fourth_moment_card_bound (k : ℕ) (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ 4 ∂latticeHaar) ≤
        C * (Fintype.card α : ℝ)^2 * P^ε * W^4 := by
  obtain ⟨A, hA, hdiv⟩ := nodeDivisorMaximum_rpow_bound (K := K) k (by omega) hε
  let C : ℝ := (k : ℝ)^2 + (k - 1 : ℕ) * A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP α inst nodes hinj hbox w W hW hw
  have hp : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hd := hdiv P hP nodes hbox
  have hcoeff : (k : ℝ)^2 + (k - 1 : ℕ) * (nodeDivisorMaximum nodes k : ℝ) ≤ C * P^ε := by
    dsimp [C]
    have hmul := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ (k - 1 : ℕ) by positivity)
    have hsq := mul_le_mul_of_nonneg_left hp (sq_nonneg (k : ℝ))
    nlinarith
  calc
    (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ 4 ∂latticeHaar) ≤
        ((k : ℝ)^2 + (k - 1 : ℕ) * (nodeDivisorMaximum nodes k : ℝ)) *
          (Fintype.card α : ℝ)^2 * W^4 :=
      numberField_monomial_fourth_moment_le K nodes hinj k hk w W hW hw
    _ ≤ (C * P^ε) * (Fintype.card α : ℝ)^2 * W^4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity)
    _ = _ := by ring

/-- Actual monomial fourth moment in the volume scale X=P^[K:Q]. -/
theorem numberField_fourth_moment_bound (k : ℕ) (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ 4 ∂latticeHaar) ≤
        C * ((P ^ Module.finrank ℚ K : ℝ) ^ (2 + ε)) * W^4 := by
  let d : ℕ := Module.finrank ℚ K
  have hd : (0 : ℝ) < d := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  obtain ⟨A, hA, hmoment⟩ := numberField_fourth_moment_card_bound (K := K) k hk
    (show 0 < (d : ℝ) * ε from mul_pos hd hε)
  let B : ℝ := 2 * (3 : ℝ)^d
  refine ⟨A * B^2, by dsimp [B]; positivity, ?_⟩
  intro P hP α inst nodes hinj hbox w W hW hw
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hcard : (Fintype.card α : ℝ) ≤ B * P^d := by
    have h := integer_box_card_bound (Finset.univ.image nodes) P hP (by
      intro x hx v
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact hbox a v)
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using h
  have hcsq : (Fintype.card α : ℝ)^2 ≤ (B * P^d)^2 :=
    pow_le_pow_left₀ (by positivity) hcard _
  have hpower : (P^d)^2 * P^((d : ℝ)*ε) = (P^d : ℝ)^(2+ε) := by
    rw [Real.rpow_add (by positivity), Real.rpow_two, ← Real.rpow_natCast P d,
      ← Real.rpow_mul hPpos.le]
  calc
    (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ 4 ∂latticeHaar) ≤
        A * (Fintype.card α : ℝ)^2 * P^((d : ℝ)*ε) * W^4 :=
      hmoment P hP nodes hinj hbox w W hW hw
    _ ≤ A * (B * P^d)^2 * P^((d : ℝ)*ε) * W^4 := by gcongr
    _ = (A * B^2) * ((P^d)^2 * P^((d : ℝ)*ε)) * W^4 := by ring
    _ = _ := by rw [hpower]

end WaringSiegel.WSL2
