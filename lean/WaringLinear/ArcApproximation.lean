import WaringLinear.PeriodicCompletion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp

/-! # The archimedean integral in the free-cofactor major arcs -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators Interval
namespace WaringLinear

def monomialWeight (c : ℝ) (k : ℕ) (x : ℝ) : ℂ := Complex.exp (↑(c*x^k)*Complex.I)

theorem continuous_monomialWeight (c : ℝ) (k : ℕ) :
    Continuous (monomialWeight c k) := by unfold monomialWeight; fun_prop

theorem monomial_riemann_sum_error (c : ℝ) (k N : ℕ) :
    ‖(∑ n ∈ range N, monomialWeight c k n) -
      ∫ x in (0:ℝ)..N, monomialWeight c k x‖ ≤ 2*|c| * (N:ℝ)^k := by
  let w := monomialWeight c k
  have hc := continuous_monomialWeight c k
  have hpart := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := w) (a := fun i : ℕ => (i:ℝ)) (n := N) (fun i _ => hc.intervalIntegrable _ _)
  have hpiece (i : ℕ) : ‖w i - ∫ x in (i:ℝ)..((i+1:ℕ):ℝ), w x‖ ≤
      2*|c| * (((i+1:ℕ):ℝ)^k-(i:ℝ)^k) := by
    have hcall (x : ℝ) (hx : x ∈ Set.uIoc (i:ℝ) ((i+1:ℕ):ℝ)) :
        ‖w i-w x‖ ≤ 2*|c| * (((i+1:ℕ):ℝ)^k-(i:ℝ)^k) := by
      rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ i)] at hx
      have hbase := real_twist_lipschitz (c*(i:ℝ)^k) (c*x^k)
      have hu := pow_le_pow_left₀ (Nat.cast_nonneg i) hx.1.le k
      have hx0 : 0≤x := (Nat.cast_nonneg i).trans hx.1.le
      have hl := pow_le_pow_left₀ hx0 hx.2 k
      rw [←mul_sub,abs_mul,abs_of_nonpos (sub_nonpos.mpr hu),←mul_assoc] at hbase
      exact hbase.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hcall
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const] at hh
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,one_smul,abs_one,mul_one] using hh
  change ‖(∑ n ∈ range N,w n)-(∫ x in (0:ℝ)..N,w x)‖ ≤ _
  rw [show (0:ℝ) = ((0:ℕ):ℝ) by simp,←hpart,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun i _ => hpiece i)).trans
  rw [←mul_sum,Finset.sum_range_sub (fun n : ℕ => (n:ℝ)^k)]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (pow_nonneg (Nat.cast_nonneg _) _)) (by positivity)

/-- The complete periodic mean times the actual monomial oscillatory integral
approximates the twisted sum. Only the period and total phase variation enter. -/
theorem polynomial_major_arc_approximation (z : ℕ → ℂ) (q N k : ℕ) (hq : 0<q)
    (a : ℂ) (c : ℝ) (ha : ‖a‖≤1) (hz : ∀ n, ‖z n‖≤1)
    (hper : ∀ n, z (n+q)=z n) (hmean : ∑ n ∈ range q, z n=(q:ℂ)*a) :
    ‖(∑ n ∈ range N, monomialWeight c k n*z n) -
       a*(∫ x in (0:ℝ)..N, monomialWeight c k x)‖ ≤
       2*(q:ℝ)*(1+2*|c| * (N:ℝ)^k)+2*|c| * (N:ℝ)^k := by
  let S := ∑ n ∈ range N, monomialWeight c k n
  let T := ∑ n ∈ range N, monomialWeight c k n*z n
  let I := ∫ x in (0:ℝ)..N, monomialWeight c k x
  have hh := periodic_polynomial_completion z q N k hq a c ha hz hper hmean
  change ‖T-a*S‖≤_ at hh
  have he := monomial_riemann_sum_error c k N
  change ‖S-I‖≤_ at he
  have ident : T-a*I = (T-a*S)+a*(S-I) := by ring
  change ‖T-a*I‖≤_
  rw [ident]
  apply (norm_add_le _ _).trans
  apply add_le_add hh
  rw [Complex.norm_mul]
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using he)

#print axioms monomial_riemann_sum_error
#print axioms polynomial_major_arc_approximation
end WaringLinear
