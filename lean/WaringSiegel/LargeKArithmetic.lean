import WaringSiegel.Thresholds
import Mathlib.Data.Real.Sqrt

/-!
# Symbolic sufficient upper bound for all k≥3

These are bounds for the rational interpolation threshold. Passing from
that threshold to G_K requires the separately stated analytic/local inputs.
-/

namespace WaringSiegel.Thresholds

theorem threshold_le_q_candidate (k q : ℕ) (hq2 : 2 ≤ q) (hqk : q ≤ k) :
    (threshold k : ℝ) ≤ (k : ℝ)^2 - k - 3 +
      ((q : ℝ) + (2 * k + 2) / q) := by
  have hr1 : 1 ≤ k - q + 1 := by omega
  have hrk : k - q + 1 ≤ k := by omega
  have h := threshold_le_first k (k - q + 1) hr1 hrk
  have hcast : ((k - q + 1 : ℕ) : ℚ) = (k : ℚ) - q + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hqk]
    norm_num
  rw [hcast, first_reparametrized _ _ (by exact_mod_cast (show q ≠ 0 by omega))] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat] using h'

/-- A concrete O(1) upper bound, with no asymptotic notation or rounding ambiguity. -/
theorem sufficientVariables_explicit_upper (k : ℕ) (hk : 3 ≤ k) :
    (sufficientVariables k : ℝ) ≤
      (k : ℝ)^2 - k - 1 + 2 * Real.sqrt (2 * ((k : ℝ) + 1)) := by
  let a : ℝ := 2 * ((k : ℝ) + 1)
  let q : ℕ := ⌈Real.sqrt a⌉₊
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hs2 : (Real.sqrt a)^2 = a := Real.sq_sqrt ha
  have hsq : Real.sqrt a ≤ (q : ℝ) := Nat.le_ceil _
  have hqs : (q : ℝ) < Real.sqrt a + 1 := Nat.ceil_lt_add_one hs
  have hq2 : 2 ≤ q := by
    have htwo : (1 : ℝ) < Real.sqrt a := by dsimp [a] at hs2; nlinarith
    have : 1 < q := Nat.lt_ceil.mpr (by simpa using htwo)
    omega
  have hqk : q ≤ k := by
    apply Nat.ceil_le.mpr
    apply (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ k)).mpr
    dsimp [a]
    nlinarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hadiv : a / (q : ℝ) ≤ Real.sqrt a := by
    apply (div_le_iff₀ hqpos).mpr
    nlinarith
  have ht := threshold_le_q_candidate k q hq2 hqk
  have hf : (sufficientVariables k : ℝ) ≤ (threshold k : ℝ) + 1 := by
    unfold sufficientVariables
    rw [if_neg (by omega)]
    have hfloor : ((⌊threshold k⌋ : ℤ) : ℚ) ≤ threshold k := Int.floor_le _
    have hfloor' : ((⌊threshold k⌋ : ℤ) : ℝ) ≤ (threshold k : ℝ) := by
      exact_mod_cast hfloor
    push_cast
    linarith
  have ha' : a = 2 * (k : ℝ) + 2 := by dsimp [a]; ring
  rw [← ha'] at ht
  dsimp [a] at *
  linarith

theorem square_le_polynomial_local_bound (k : ℕ) (hk : 1 ≤ k) :
    k ^ 2 ≤ 8 * k ^ 5 := by
  have hp : k ^ 2 ≤ k ^ 5 := Nat.pow_le_pow_right hk (by decide)
  omega

theorem sufficientVariables_le_polynomial_local_bound (k : ℕ) (hk : 3 ≤ k) :
    sufficientVariables k ≤ (8 * k ^ 5 : ℕ) := by
  have h1 := sufficientVariables_le_square k hk
  have h2 := square_le_polynomial_local_bound k (by omega)
  exact h1.trans (by exact_mod_cast h2)

end WaringSiegel.Thresholds
