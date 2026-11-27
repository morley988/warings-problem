import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.Linarith

/-! # Polynomially narrow rational arcs with a free cofactor

A complete-period average separates from a real twist. The error is at
most twice the period times the endpoint norm and finite total variation.
-/

namespace WaringLinear
open scoped BigOperators
open Finset

/-- Multiplication by a unit permutes the complete residue sum. -/
theorem complete_unit_dilation {A : Type*} [Monoid A] [Fintype A]
    (u : Aˣ) (f : A → ℂ) (k : ℕ) :
    (∑ x : A, f (((u:A)*x)^k)) = ∑ x : A, f (x^k) :=
  (Equiv.sum_comp u.mulLeft (fun x : A => f (x^k)))

theorem centered_period_prefix (z : ℕ → ℂ) (q : ℕ) (hq : 0<q)
    (a : ℂ) (ha : ‖a‖≤1) (hz : ∀ n, ‖z n‖≤1)
    (hper : ∀ n, z (n+q)=z n) (hmean : ∑ n ∈ range q, z n=(q:ℂ)*a)
    (N : ℕ) : ‖∑ n ∈ range N, (z n-a)‖ ≤ 2*(q:ℝ) := by
  let u (n : ℕ) := z n-a
  have hperiod (m n : ℕ) : u (q*m+n)=u n := by
    induction m with
    | zero => simp
    | succ m ih =>
      simpa only [u,Nat.mul_succ,show (q*m+q)+n=(q*m+n)+q by omega,hper] using ih
  have hzero : ∑ n ∈ range q, u n=0 := by
    simp [u,sum_sub_distrib,hmean]
  have hblocks (m : ℕ) : ∑ n ∈ range (q*m), u n=0 := by
    induction m with
    | zero => simp
    | succ m ih => simp [Nat.mul_succ,sum_range_add,ih,hperiod,hzero]
  have hsplit : (∑ n ∈ range N, u n) = ∑ n ∈ range (N%q), u n := by
    conv_lhs => rw [←Nat.div_add_mod N q]
    rw [sum_range_add,hblocks,zero_add]
    simp only [hperiod]
  change ‖∑ n ∈ range N, u n‖≤_
  rw [hsplit]
  calc
    _ ≤ ∑ n ∈ range (N%q), ‖u n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (N%q), (2:ℝ) := sum_le_sum (fun n _ =>
      (norm_sub_le (z n) a).trans (by linarith only [hz n,ha]))
    _ ≤ _ := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      have h : (N%q:ℝ)≤q := by exact_mod_cast (Nat.mod_lt N hq).le
      linarith only [h]

theorem periodic_weight_error (z w : ℕ → ℂ) (q N : ℕ) (hq : 0<q)
    (a : ℂ) (ha : ‖a‖≤1) (hz : ∀ n, ‖z n‖≤1)
    (hper : ∀ n, z (n+q)=z n) (hmean : ∑ n ∈ range q, z n=(q:ℂ)*a) :
    ‖(∑ n ∈ range N, w n*z n)-a*(∑ n ∈ range N, w n)‖ ≤
      2*(q:ℝ)*(‖w (N-1)‖+∑ n ∈ range (N-1), ‖w (n+1)-w n‖) := by
  let u (n : ℕ) := z n-a
  let G (m : ℕ) := ∑ n ∈ range m, u n
  have hG (m) : ‖G m‖ ≤ 2*(q:ℝ) := centered_period_prefix z q hq a ha hz hper hmean m
  have hid : (∑ n ∈ range N, w n*z n)-a*(∑ n ∈ range N,w n)=
      ∑ n ∈ range N,w n • u n := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    simp only [u,smul_eq_mul,mul_sub]
    ring
  rw [hid,Finset.sum_range_by_parts]
  change ‖w (N-1)*G N-∑ i ∈ range (N-1), (w (i+1)-w i)*G (i+1)‖≤_
  have head := mul_le_mul_of_nonneg_left (hG N) (norm_nonneg (w (N-1)))
  have tail : ‖∑ i ∈ range (N-1), (w (i+1)-w i)*G (i+1)‖ ≤
      (∑ i ∈ range (N-1), ‖w (i+1)-w i‖)*(2*(q:ℝ)) := by
    rw [sum_mul]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i _
    rw [Complex.norm_mul]
    exact mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_mul]
  nlinarith only [head,tail]

theorem real_twist_lipschitz (a b : ℝ) :
    ‖Complex.exp ((a:ℂ)*Complex.I)-Complex.exp ((b:ℂ)*Complex.I)‖ ≤ 2*|a-b| := by
  let z := ((a-b:ℝ):ℂ)*Complex.I
  have hn : ‖z‖=|a-b| := by
    change ‖((a-b:ℝ):ℂ)*Complex.I‖=_
    rw [Complex.norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hbase : ‖Complex.exp z-1‖≤2*|a-b| := by
    by_cases h : ‖z‖≤1
    · simpa only [hn] using Complex.norm_exp_sub_one_le h
    · have he : ‖Complex.exp z‖=1 := Complex.norm_exp_ofReal_mul_I _
      apply (norm_sub_le _ _).trans
      have hone : ‖(1:ℂ)‖=1 := calc
        _ = ‖((1:ℝ):ℂ)‖ := rfl
        _ = ‖(1:ℝ)‖ := Complex.norm_real _
        _ = 1 := by rw [Real.norm_eq_abs,abs_one]
      rw [he,hone,←hn]
      linarith only [not_le.mp h]
  have hid : Complex.exp ((a:ℂ)*Complex.I)-Complex.exp ((b:ℂ)*Complex.I) =
      Complex.exp ((b:ℂ)*Complex.I)*(Complex.exp z-1) := by
    rw [mul_sub,mul_one,←Complex.exp_add]
    have harg : (b:ℂ)*Complex.I+z=(a:ℂ)*Complex.I := by dsimp [z]; push_cast; ring
    rw [harg]
  rwa [hid,Complex.norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]

theorem polynomial_twist_variation (c : ℝ) (k N : ℕ) :
    (∑ i ∈ range N, ‖Complex.exp (↑(c*((i+1:ℕ):ℝ)^k)*Complex.I)-
       Complex.exp (↑(c*(i:ℝ)^k)*Complex.I)‖) ≤ 2*|c| * (N:ℝ)^k := by
  have step (i : ℕ) : ‖Complex.exp (↑(c*((i+1:ℕ):ℝ)^k)*Complex.I)-
       Complex.exp (↑(c*(i:ℝ)^k)*Complex.I)‖ ≤ 2*|c| * (((i+1:ℕ):ℝ)^k-(i:ℝ)^k) := by
    have h := real_twist_lipschitz (c*((i+1:ℕ):ℝ)^k) (c*(i:ℝ)^k)
    have hmono : (i:ℝ)^k ≤ ((i+1:ℕ):ℝ)^k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ i) _
    rwa [←mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hmono),←mul_assoc] at h
  apply (sum_le_sum (fun i _ => step i)).trans
  rw [←mul_sum,Finset.sum_range_sub (fun n : ℕ => (n:ℝ)^k)]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (pow_nonneg (Nat.cast_nonneg _) _)) (by positivity)

/-- The error at a polynomially narrow arc, prior to replacing the final
ordinary polynomial sum by its archimedean integral. -/
theorem periodic_polynomial_completion (z : ℕ → ℂ) (q N k : ℕ) (hq : 0<q)
    (a : ℂ) (c : ℝ) (ha : ‖a‖≤1) (hz : ∀ n, ‖z n‖≤1)
    (hper : ∀ n, z (n+q)=z n) (hmean : ∑ n ∈ range q, z n=(q:ℂ)*a) :
    let w := fun n : ℕ => Complex.exp (↑(c*(n:ℝ)^k)*Complex.I)
    ‖(∑ n ∈ range N, w n*z n)-a*(∑ n ∈ range N, w n)‖ ≤
      2*(q:ℝ)*(1+2*|c| * (N:ℝ)^k) := by
  dsimp only
  let w := fun n : ℕ => Complex.exp (↑(c*(n:ℝ)^k)*Complex.I)
  apply (periodic_weight_error z w q N hq a ha hz hper hmean).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show ‖w (N-1)‖=1 from Complex.norm_exp_ofReal_mul_I _]
  apply add_le_add_left
  apply (polynomial_twist_variation c k (N-1)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le N 1) k

#print axioms complete_unit_dilation
#print axioms periodic_polynomial_completion
#print axioms centered_period_prefix
#print axioms periodic_weight_error
#print axioms polynomial_twist_variation
end WaringLinear
