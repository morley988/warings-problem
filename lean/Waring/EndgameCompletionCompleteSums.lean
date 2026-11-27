import Waring.EndgameCompletionMajor
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Basic

/-!
# Elementary prime-modulus bounds for complete monomial sums

Multiplicative rescaling makes a complete monomial sum constant on power
cosets. Additive orthogonality and the root bound for a polynomial then give
square-root cancellation, with a degree-dependent constant. This argument
needs neither a Gauss-sum estimate nor an assumed Weil bound.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Waring.EndgameCompletion
open QuadraticModulation

theorem card_pow_fiber_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (k : ℕ) (hk : 0 < k) (b : K) :
    ((Finset.univ : Finset K).filter (fun x => x^k=b)).card ≤ k := by
  have hpoly : (Polynomial.X^k-Polynomial.C b : Polynomial K) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hk b
  have hcard := Polynomial.card_le_degree_of_subset_roots
    (p := (Polynomial.X^k-Polynomial.C b : Polynomial K))
    (Z := (Finset.univ : Finset K).filter (fun x => x^k=b)) (by
      intro x hx
      rw [Polynomial.mem_roots hpoly]
      simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using (Finset.mem_filter.mp hx).2)
  simpa only [Polynomial.natDegree_X_pow_sub_C] using hcard

/-- Summing a nonnegative weight along a map with fibers of size at most `d`.
The target is the full finite type, so no surjectivity assumption is needed. -/
theorem sum_comp_le_fiber_bound {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Finset ι) (f : ι → κ) (w : κ → ℝ) (d : ℕ)
    (hw : ∀ y, 0 ≤ w y) (hf : ∀ y, (A.filter (fun x => f x=y)).card ≤ d) :
    (∑ x ∈ A, w (f x)) ≤ (d : ℝ)*∑ y, w y := by
  rw [← Finset.sum_fiberwise' A f w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hf y) (hw y)

/-- Complete monomial sums on a residue ring. -/
def completeMonomialSumMod (q : ℕ) [NeZero q] (k : ℕ) (a : ZMod q) : ℂ :=
  ∑ x : ZMod q, ZMod.stdAddChar (a*x^k)

theorem stdAddChar_mul_sum (q : ℕ) [NeZero q] (t : ZMod q) :
    (∑ a : ZMod q, ZMod.stdAddChar (t*a)) = if t=0 then (q : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht, AddChar.map_zero_eq_one, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)

theorem completeMonomialSumMod_norm_sq (q : ℕ) [NeZero q] (k : ℕ) (a : ZMod q) :
    ((‖completeMonomialSumMod q k a‖^2 : ℝ) : ℂ) =
      ∑ x : ZMod q, ∑ y : ZMod q, ZMod.stdAddChar (a*(x^k-y^k)) := by
  unfold completeMonomialSumMod
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Exact finite additive orthogonality for the complete-sum second moment. -/
theorem completeMonomialSumMod_second_moment (q : ℕ) [NeZero q] (k : ℕ) :
    (∑ a : ZMod q, ‖completeMonomialSumMod q k a‖^2) =
      (q : ℝ)*∑ x : ZMod q,
        (((Finset.univ : Finset (ZMod q)).filter (fun y => y^k=x^k)).card : ℝ) := by
  have hc : ((∑ a : ZMod q, ‖completeMonomialSumMod q k a‖^2 : ℝ) : ℂ) =
      (q : ℂ)*∑ x : ZMod q,
        (((Finset.univ : Finset (ZMod q)).filter (fun y => y^k=x^k)).card : ℂ) := by
    simp only [Complex.ofReal_sum, completeMonomialSumMod_norm_sq]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x : ZMod q, ∑ y : ZMod q, ∑ a : ZMod q,
          ZMod.stdAddChar ((x^k-y^k)*a) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        simp only [mul_comm]
      _ = ∑ x : ZMod q, ∑ y : ZMod q, if y^k=x^k then (q : ℂ) else 0 := by
        simp only [stdAddChar_mul_sum, sub_eq_zero, eq_comm]
      _ = _ := by
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  exact_mod_cast hc

theorem completeMonomialSumMod_second_moment_le {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 0 < k) :
    (∑ a : ZMod p, ‖completeMonomialSumMod p k a‖^2) ≤ (k : ℝ)*p^2 := by
  rw [completeMonomialSumMod_second_moment]
  calc
    _ ≤ (p : ℝ)*∑ _x : ZMod p, (k : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro x _
      exact_mod_cast card_pow_fiber_le k hk (x^k)
    _ = _ := by simp [ZMod.card]; ring

theorem completeMonomialSumMod_scale {p : ℕ} [Fact p.Prime]
    (k : ℕ) (a u : ZMod p) (hu : u ≠ 0) :
    completeMonomialSumMod p k (a*u^k) = completeMonomialSumMod p k a := by
  unfold completeMonomialSumMod
  apply Fintype.sum_equiv (Equiv.mulLeft₀ u hu)
  intro x
  simp only [Equiv.mulLeft₀_apply, mul_pow, mul_assoc]

theorem completeMonomialSumMod_prime_sq_le {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 0 < k) {a : ZMod p} (ha : a ≠ 0) :
    ‖completeMonomialSumMod p k a‖^2 ≤ 2*(k : ℝ)^2*p := by
  let A : Finset (ZMod p) := Finset.univ.erase 0
  have hfiber (b : ZMod p) : (A.filter (fun x => a*x^k=b)).card ≤ k := by
    apply le_trans (Finset.card_le_card (t := (Finset.univ : Finset (ZMod p)).filter
      (fun x => x^k=b/a)) ?_) (card_pow_fiber_le k hk (b/a))
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (eq_div_iff ha).mpr ?_⟩
    simpa only [mul_comm] using (Finset.mem_filter.mp hx).2
  have hweighted := sum_comp_le_fiber_bound A (fun x => a*x^k)
    (fun b => ‖completeMonomialSumMod p k b‖^2) k (fun b => sq_nonneg _) hfiber
  have hleft : (∑ x ∈ A, ‖completeMonomialSumMod p k (a*x^k)‖^2) =
      ((p : ℝ)-1)*‖completeMonomialSumMod p k a‖^2 := by
    have heq : ∀ x ∈ A, completeMonomialSumMod p k (a*x^k) = completeMonomialSumMod p k a :=
      fun x hx => completeMonomialSumMod_scale k a x (Finset.mem_erase.mp hx).1
    simp_rw [Finset.sum_congr rfl (fun x hx => congrArg (fun z : ℂ => ‖z‖^2) (heq x hx))]
    simp only [A, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [Nat.cast_sub (show 1 ≤ p from (Fact.out : p.Prime).one_lt.le), Nat.cast_one]
  rw [hleft] at hweighted
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp1 : 0 < (p : ℝ)-1 := by linarith
  apply (mul_le_mul_iff_right₀ hp1).mp
  calc
    _ ≤ (k : ℝ)*(k*p^2) := hweighted.trans
      (mul_le_mul_of_nonneg_left (completeMonomialSumMod_second_moment_le k hk) (Nat.cast_nonneg _))
    _ = (k : ℝ)^2*p^2 := by ring
    _ ≤ (k : ℝ)^2*((p-1)*(2*p)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith
    _ = _ := by ring

theorem stdAddChar_monomial_nat (q : ℕ) [NeZero q] (k : ℕ) (a : ℤ) (n : ℕ) :
    ZMod.stdAddChar ((a : ZMod q)*(n : ZMod q)^k) = e ((a : ℝ)/q*(n : ℝ)^k) := by
  rw [show (a : ZMod q)*(n : ZMod q)^k = ((a*(n : ℤ)^k : ℤ) : ZMod q) by push_cast; rfl,
    ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

/-- Exact adapter from residue-ring characters back to the positive
representatives in the ordinary major-arc approximation. -/
theorem completeMonomialSum_eq_mod (k : ℕ) (a : ℤ) (q : ℕ) [NeZero q] :
    completeMonomialSum k a q = completeMonomialSumMod q k (a : ZMod q) := by
  unfold completeMonomialSum completeMonomialSumMod
  apply Finset.sum_bij (fun n _ => ((n+1 : ℕ) : ZMod q))
  · intro n _
    exact Finset.mem_univ _
  · intro n hn m hm hnm
    have hcast : (n : ZMod q) = (m : ZMod q) := by
      apply add_right_cancel (b := (1 : ZMod q))
      simpa only [Nat.cast_add, Nat.cast_one] using hnm
    have hmod := (ZMod.natCast_eq_natCast_iff' n m q).mp hcast
    simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hn),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hm)] using hmod
  · intro x _
    refine ⟨(x-1).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val, sub_add_cancel]
  · intro n _
    exact (stdAddChar_monomial_nat q k a (n+1)).symm

/-- A proved square-root bound for prime-modulus complete sums in the exact
representation used by `ordinary_rational_approximation`. -/
theorem completeMonomialSum_prime_sq_le {p : ℕ} (hp : p.Prime)
    (k : ℕ) (hk : 0 < k) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    ‖completeMonomialSum k a p‖^2 ≤ 2*(k : ℝ)^2*p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [completeMonomialSum_eq_mod]
  apply completeMonomialSumMod_prime_sq_le k hk
  simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using ha

#print axioms completeMonomialSumMod_second_moment
#print axioms completeMonomialSumMod_prime_sq_le
#print axioms completeMonomialSum_prime_sq_le

end Waring.EndgameCompletion
