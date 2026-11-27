import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reused real Holder interpolation from the classical G(8)/G(9) verification

The two proofs below are adapted only in namespace from the recovered
classical project Waring/Holder.lean (integral_pow_interpolation) and
Waring/SmoothInterpolation.lean (interpolated_power_bound). They concern
arbitrary measures and nonnegative functions, so they apply directly to the
actual number-field trace Haar measure restricted to minor arcs.

Source SHA-256:
Holder.lean: 51dbb5bdf6f958955cf972f96c7c61bf5df3f8bf2ecd7fe25402c5c609d2598f
SmoothInterpolation.lean: b26742249c756726a058be6843bc5378c1aa777e4d9c44e07aabe98e1a55c531
-/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace WaringSiegel.WSL3

theorem integral_pow_interpolation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p p₀ p₁ : ℕ} {t : ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hp : Integrable (fun x => f x ^ p) μ)
    (hp₀ : Integrable (fun x => f x ^ p₀) μ)
    (hp₁ : Integrable (fun x => f x ^ p₁) μ)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (horder : (p : ℝ) = (p₀ : ℝ) * t + (p₁ : ℝ) * (1 - t)) :
    (∫ x, f x ^ p ∂μ) ≤
      (∫ x, f x ^ p₀ ∂μ) ^ t * (∫ x, f x ^ p₁ ∂μ) ^ (1 - t) := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hn (r : ℕ) : 0 ≤ᵐ[μ] (fun x => f x ^ r) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (hf x) r)
  have hid (x : α) :
      (f x ^ p₀) ^ t * (f x ^ p₁) ^ (1 - t) = f x ^ p := by
    rw [← Real.rpow_natCast_mul (hf x), ← Real.rpow_natCast_mul (hf x),
      ← Real.rpow_add_of_nonneg (hf x) (mul_nonneg (Nat.cast_nonneg _) ht₀)
        (mul_nonneg (Nat.cast_nonneg _) ht'), ← horder, Real.rpow_natCast]
  have H := ENNReal.lintegral_mul_norm_pow_le
    hp₀.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hp₁.aestronglyMeasurable.aemeasurable.ennreal_ofReal ht₀ ht' (by ring : t + (1-t) = 1)
  have hid' (x : α) :
      ENNReal.ofReal (f x ^ p₀) ^ t * ENNReal.ofReal (f x ^ p₁) ^ (1-t) =
        ENNReal.ofReal (f x ^ p) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (hf x) _) ht₀,
      ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (hf x) _) ht',
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg (hf x) _) _), hid]
  simp_rw [hid'] at H
  rw [← ofReal_integral_eq_lintegral_ofReal hp (hn p),
    ← ofReal_integral_eq_lintegral_ofReal hp₀ (hn p₀),
    ← ofReal_integral_eq_lintegral_ofReal hp₁ (hn p₁)] at H
  have hi₀ : 0 ≤ ∫ x, f x ^ p₀ ∂μ := integral_nonneg_of_ae (hn p₀)
  have hi₁ : 0 ≤ ∫ x, f x ^ p₁ ∂μ := integral_nonneg_of_ae (hn p₁)
  rw [ENNReal.ofReal_rpow_of_nonneg hi₀ ht₀,
    ENNReal.ofReal_rpow_of_nonneg hi₁ ht',
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hi₀ _)] at H
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hi₀ _) (Real.rpow_nonneg hi₁ _))).mp H

theorem interpolated_power_bound {x y C P lam mu ε t : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 < C) (hP : 0 < P)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hxb : x ≤ C * P ^ (lam + ε)) (hyb : y ≤ C * P ^ (mu + ε)) :
    x ^ t * y ^ (1 - t) ≤ C * P ^ (lam * t + mu * (1 - t) + ε) := by
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  calc
    x ^ t * y ^ (1 - t) ≤
        (C * P ^ (lam + ε)) ^ t * (C * P ^ (mu + ε)) ^ (1 - t) :=
      mul_le_mul (Real.rpow_le_rpow hx hxb ht₀) (Real.rpow_le_rpow hy hyb ht')
        (Real.rpow_nonneg hy _) (Real.rpow_nonneg
          (mul_nonneg hC.le (Real.rpow_nonneg hP.le _)) _)
    _ = (C ^ t * C ^ (1 - t)) *
        (P ^ ((lam + ε) * t) * P ^ ((mu + ε) * (1 - t))) := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg hP.le _),
        Real.mul_rpow hC.le (Real.rpow_nonneg hP.le _),
        ← Real.rpow_mul hP.le, ← Real.rpow_mul hP.le]
      ring
    _ = C * P ^ (lam * t + mu * (1 - t) + ε) := by
      rw [← Real.rpow_add hC, ← Real.rpow_add hP]
      have hsum : t + (1 - t) = 1 := by ring
      have hexponent : (lam + ε) * t + (mu + ε) * (1 - t) =
          lam * t + mu * (1 - t) + ε := by ring
      rw [hsum, Real.rpow_one, hexponent]


#print axioms integral_pow_interpolation
#print axioms interpolated_power_bound
end WaringSiegel.WSL3
