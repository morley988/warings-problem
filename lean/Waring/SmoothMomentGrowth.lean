import Waring.SmoothMoments
import Mathlib.Tactic.Ring

/-!
# Raising the moment order with the trivial pointwise bound

The actual Weyl sum has norm at most `P`. Thus increasing the natural moment
order from `p` to `q` costs at most `P^(q-p)`. In admissible-excess notation this
preserves the same excess. All constants and the smoothness parameter remain
uniform in the defining range.
-/

noncomputable section
open MeasureTheory
namespace Waring.SmoothMoments

theorem smoothMoment_order_growth (k p q : ℕ) {P : ℝ} (R : ℝ)
    (hpq : p ≤ q) (hP : 0 ≤ P) :
    smoothMoment k q P R ≤ P^(q-p)*smoothMoment k p P R := by
  have hpoint (α : ℝ) :
      ‖smoothWeyl k P R α‖^q ≤ P^(q-p)*‖smoothWeyl k P R α‖^p := by
    calc
      ‖smoothWeyl k P R α‖^q =
          ‖smoothWeyl k P R α‖^(q-p)*‖smoothWeyl k P R α‖^p := by
        rw [← pow_add, Nat.sub_add_cancel hpq]
      _ ≤ P^(q-p)*‖smoothWeyl k P R α‖^p :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (norm_smoothWeyl_le k R α hP) _)
          (pow_nonneg (norm_nonneg _) _)
  calc
    smoothMoment k q P R ≤
        ∫ α in (0 : ℝ)..1, P^(q-p)*‖smoothWeyl k P R α‖^p :=
      intervalIntegral.integral_mono zero_le_one (smoothMoment_integrable k q P R)
        ((smoothMoment_integrable k p P R).const_mul _) hpoint
    _ = P^(q-p)*smoothMoment k p P R := by
      rw [intervalIntegral.integral_const_mul]
      rfl

theorem admissibleExponent_order_growth {k p q : ℕ} {lam : ℝ}
    (h : AdmissibleExponent k p lam) (hpq : p ≤ q) :
    AdmissibleExponent k q (lam+(q-p : ℕ)) := by
  intro ε hε
  rcases h ε hε with ⟨η, hη, C, hC, P₀, hP₀, hb⟩
  refine ⟨η, hη, C, hC, P₀, hP₀, ?_⟩
  intro P hP R hR hRP
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  calc
    smoothMoment k q P R ≤ P^(q-p)*smoothMoment k p P R :=
      smoothMoment_order_growth k p q R hpq hPpos.le
    _ ≤ P^(q-p)*(C*P^(lam+ε)) :=
      mul_le_mul_of_nonneg_left (hb P hP R hR hRP) (pow_nonneg hPpos.le _)
    _ = C*P^((lam+(q-p : ℕ))+ε) := by
      rw [← Real.rpow_natCast P (q-p), mul_left_comm,
        ← Real.rpow_add hPpos]
      congr 1
      congr 1
      ring

theorem admissibleExcess_order_growth {k p q : ℕ} {Δ : ℝ}
    (h : AdmissibleExcess k p Δ) (hpq : p ≤ q) :
    AdmissibleExcess k q Δ := by
  have hg := admissibleExponent_order_growth h hpq
  have heq : ((p : ℝ)-k+Δ)+(q-p : ℕ) = (q : ℝ)-k+Δ := by
    rw [Nat.cast_sub hpq]
    ring
  rw [heq] at hg
  exact hg

#print axioms smoothMoment_order_growth
#print axioms admissibleExcess_order_growth
end Waring.SmoothMoments
