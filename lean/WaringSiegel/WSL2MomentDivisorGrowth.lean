import WaringSiegel.WSL2MomentDivisorBridge
import WaringSiegel.WSL2UnitLogGrowth

/-!
# Epsilon bounds for boxed divisors of arbitrary polynomial-size targets

The target may be any nonzero algebraic integer. Its only size assumption
is the explicit polynomial norm bound; the constants are uniform in that
target, the finite divisor set, and the box radius.
-/

noncomputable section
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- Actual ring divisors in the box 2P have arbitrary small-power growth
whenever the target norm is bounded by A P^m. -/
theorem ring_divisor_polynomial_norm_rpow_bound (m : ℕ) (A : ℝ) (hA : 0 < A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ a : 𝓞 K, a ≠ 0 →
      absNorm a ≤ A * P ^ m → ∀ T : Finset (𝓞 K),
      (∀ h ∈ T, h ∣ a) →
      (∀ h ∈ T, ∀ v : NumberField.InfinitePlace K, v (h : K) ≤ 2 * P) →
      (T.card : ℝ) ≤ C * P ^ ε := by
  let δ : ℝ := ε / (2 * ((m : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨D, hD, hdiv⟩ := ring_divisor_box_bound (K := K) hδ
  obtain ⟨B, hB, hlog⟩ := exists_one_add_log_pow_le_rpow
    (NumberField.Units.rank K) (show 0 < ε / 2 by linarith)
  let C : ℝ := D * A ^ δ * B * (2 : ℝ) ^ (ε / 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP a ha hanorm T hTdiv hTbox
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hL : 1 ≤ 2 * P := by linarith
  have hlog0 : 0 ≤ (1 + Real.log (2 * P)) ^ NumberField.Units.rank K := by
    apply pow_nonneg
    linarith [Real.log_nonneg hL]
  have hn : (A * P ^ m : ℝ) ^ δ = A ^ δ * P ^ ((m : ℝ) * δ) := by
    rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_natCast P m,
      ← Real.rpow_mul hPpos.le]
  have hexp : (m : ℝ) * δ + ε / 2 ≤ ε := by
    have he : ((m : ℝ) + 1) * δ = ε / 2 := by
      dsimp [δ]
      field_simp
    nlinarith
  calc
    (T.card : ℝ) ≤ D * absNorm a ^ δ *
        (1 + Real.log (2 * P)) ^ NumberField.Units.rank K :=
      hdiv (2 * P) hL a ha T hTdiv hTbox
    _ ≤ D * (A * P ^ m : ℝ) ^ δ *
        (1 + Real.log (2 * P)) ^ NumberField.Units.rank K :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (absNorm_nonneg a) hanorm hδ.le) hD.le)
        hlog0
    _ ≤ D * (A * P ^ m : ℝ) ^ δ * (B * (2 * P) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (hlog (2 * P) hL) (by positivity)
    _ = C * (P ^ ((m : ℝ) * δ) * P ^ (ε / 2)) := by
      rw [hn, Real.mul_rpow (by norm_num) hPpos.le]
      dsimp [C]
      ring
    _ = C * P ^ ((m : ℝ) * δ + ε / 2) := by rw [Real.rpow_add hPpos]
    _ ≤ C * P ^ ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hexp) (by dsimp [C]; positivity)

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.ring_divisor_polynomial_norm_rpow_bound
