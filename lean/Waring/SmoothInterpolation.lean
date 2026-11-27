import Waring.SmoothMoments
import Waring.Holder
import Mathlib.Tactic.Ring

/-!
# Holder interpolation preserves actual admissible smooth moments

These are semantic closure theorems for the finite sums and Lebesgue integrals
in `SmoothMoments`. They do not assume that any improved table entry is
admissible. They will connect valid two-point interpolation witnesses from the
finite certificate to admissibility once its input estimates are proved.
-/

noncomputable section
open MeasureTheory

namespace Waring.SmoothMoments

/-- Holder's inequality for two actual smooth moments, including weights zero
and one. The order equality is in the real numbers, while all moment orders
are natural numbers. -/
theorem smoothMoment_interpolation (k p p₀ p₁ : ℕ) (P R : ℝ) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (horder : (p : ℝ) = (p₀ : ℝ) * t + (p₁ : ℝ) * (1 - t)) :
    smoothMoment k p P R ≤
      (smoothMoment k p₀ P R) ^ t * (smoothMoment k p₁ P R) ^ (1 - t) := by
  unfold smoothMoment
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exact Waring.Holder.integral_pow_interpolation (fun α => norm_nonneg _)
    (smoothMoment_integrable k p P R).1
    (smoothMoment_integrable k p₀ P R).1
    (smoothMoment_integrable k p₁ P R).1 ht₀ ht₁ horder

/-- Interpolating two bounds with a common positive constant keeps that same
constant and the same epsilon loss. -/
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

/-- An admissible full exponent at an intermediate natural order is given by
the matching convex combination of two admissible full exponents. -/
theorem admissibleExponent_interpolation {k p p₀ p₁ : ℕ} {lam mu t : ℝ}
    (h₀ : AdmissibleExponent k p₀ lam) (h₁ : AdmissibleExponent k p₁ mu)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (horder : (p : ℝ) = (p₀ : ℝ) * t + (p₁ : ℝ) * (1 - t)) :
    AdmissibleExponent k p (lam * t + mu * (1 - t)) := by
  intro ε hε
  rcases admissibleExponent_pair h₀ h₁ hε with ⟨η, hη, C, hC, P₀, hP₀, hb⟩
  refine ⟨η, hη, C, hC, P₀, hP₀, ?_⟩
  intro P hP R hR hRP
  rcases hb P hP R hR hRP with ⟨hb₀, hb₁⟩
  exact (smoothMoment_interpolation k p p₀ p₁ P R ht₀ ht₁ horder).trans
    (interpolated_power_bound (smoothMoment_nonneg _ _ _ _)
      (smoothMoment_nonneg _ _ _ _) hC (zero_lt_one.trans_le (hP₀.trans hP))
      ht₀ ht₁ hb₀ hb₁)

/-- The same closure in the manuscript's excess notation. -/
theorem admissibleExcess_interpolation {k p p₀ p₁ : ℕ} {δ₀ δ₁ t : ℝ}
    (h₀ : AdmissibleExcess k p₀ δ₀) (h₁ : AdmissibleExcess k p₁ δ₁)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (horder : (p : ℝ) = (p₀ : ℝ) * t + (p₁ : ℝ) * (1 - t)) :
    AdmissibleExcess k p (δ₀ * t + δ₁ * (1 - t)) := by
  have h := admissibleExponent_interpolation h₀ h₁ ht₀ ht₁ horder
  have heq : ((p₀ : ℝ) - k + δ₀) * t + ((p₁ : ℝ) - k + δ₁) * (1 - t) =
      (p : ℝ) - k + (δ₀ * t + δ₁ * (1 - t)) := by
    rw [horder]
    ring
  rw [heq] at h
  exact h

#print axioms smoothMoment_interpolation
#print axioms admissibleExponent_interpolation
#print axioms admissibleExcess_interpolation

end Waring.SmoothMoments
