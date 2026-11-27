import Waring.Representation
import Waring.Orthogonality

/-!
# The circle integral equals the actual finite Waring representation count

The cutoff `B = n` is deliberately generous: each variable lies in `1,...,n`.
This exact identity supplies a genuine link from an analytic integral to the
representation predicate used in `WaringBound`. It contains no minor-arc or
major-arc estimate.
-/

noncomputable section

open scoped BigOperators

namespace Waring

/-- The full degree-`k` exponential sum over `1,...,B`, in circle-character notation. -/
def fullWeylPolynomial (k B : ℕ) (α : ℝ) : ℂ :=
  ∑ j : Fin B, fourier ((((j.val + 1) ^ k : ℕ) : ℤ)) (α : AddCircle (1 : ℝ))

/-- Fourier orthogonality yields the exact finite Waring count, for every `k,s,n`. -/
theorem integral_eq_representationCount (k s n : ℕ) :
    (∫ α in (0 : ℝ)..1,
      fullWeylPolynomial k n α ^ s * fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))) =
      (representationCount k s n : ℂ) := by
  classical
  have h := interval_integral_power_frequency_coefficient
    (fun j : Fin n => (((j.val + 1) ^ k : ℕ) : ℤ)) s (n : ℤ)
  have hpred (f : Fin s → Fin n) :
      (∑ i, ((((f i).val + 1) ^ k : ℕ) : ℤ)) = (n : ℤ) ↔
        ∑ i, ((f i).val + 1) ^ k = n := by
    rw [← Nat.cast_sum]
    exact Nat.cast_inj
  simp_rw [hpred] at h
  exact h

/-- The real part of the circle integral is the actual nonnegative integer count. -/
theorem integral_re_eq_representationCount (k s n : ℕ) :
    (∫ α in (0 : ℝ)..1,
      fullWeylPolynomial k n α ^ s * fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))).re =
      (representationCount k s n : ℝ) := by
  rw [integral_eq_representationCount]
  simp

end Waring
