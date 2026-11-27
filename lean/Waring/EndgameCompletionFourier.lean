import Waring.EndgameCompletionTwistedCRT

/-!
# Exact finite Fourier completion

The full twisted sums are the actual finite Fourier coefficients of the
rational monomial phase. This file retains every nonzero frequency and
isolates the ordinary integral model by an exact identity.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.EndgameCompletion
open QuadraticModulation

theorem twistedMonomialSumMod_fourier_inversion (q k : ℕ) [NeZero q]
    (a y : ZMod q) :
    (∑ b : ZMod q, twistedMonomialSumMod q k a b*ZMod.stdAddChar (-b*y)) =
      (q : ℂ)*ZMod.stdAddChar (a*y^k) := by
  unfold twistedMonomialSumMod
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : ZMod q, ZMod.stdAddChar (a*x^k)*
        ∑ b : ZMod q, ZMod.stdAddChar ((x-y)*b) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [← AddChar.map_add_eq_mul,← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = (q : ℂ)*ZMod.stdAddChar (a*y^k) := by
      simp only [stdAddChar_mul_sum,sub_eq_zero]
      simp [mul_comm]

def completedLinearSum (q : ℕ) [NeZero q] (A : Finset ℕ) (w : ℕ → ℂ) (b : ZMod q) : ℂ :=
  ∑ n ∈ A, w n*ZMod.stdAddChar (-b*(n : ZMod q))

def rationalWeightedSum (q k : ℕ) [NeZero q] (a : ZMod q)
    (A : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ A, ZMod.stdAddChar (a*(n : ZMod q)^k)*w n

theorem rationalWeightedSum_completion (q k : ℕ) [NeZero q] (a : ZMod q)
    (A : Finset ℕ) (w : ℕ → ℂ) :
    rationalWeightedSum q k a A w = (q : ℂ)⁻¹*
      ∑ b : ZMod q, twistedMonomialSumMod q k a b*completedLinearSum q A w b := by
  have hq : (q : ℂ)≠0 := by exact_mod_cast (NeZero.ne q)
  apply mul_left_cancel₀ (a := (q : ℂ)) hq
  rw [← mul_assoc,mul_inv_cancel₀ hq,one_mul]
  unfold rationalWeightedSum completedLinearSum
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have hf := twistedMonomialSumMod_fourier_inversion q k a (n : ZMod q)
  calc
    _ = (q*ZMod.stdAddChar (a*(n : ZMod q)^k))*w n := by ring
    _ = (∑ b : ZMod q, twistedMonomialSumMod q k a b*ZMod.stdAddChar (-b*(n : ZMod q)))*w n :=
      congrArg (fun z : ℂ => z*w n) hf.symm
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring

@[simp] theorem completedLinearSum_zero (q : ℕ) [NeZero q] (A : Finset ℕ) (w : ℕ → ℂ) :
    completedLinearSum q A w 0=∑ n∈A,w n := by
  simp [completedLinearSum,AddChar.map_zero_eq_one]

@[simp] theorem twistedMonomialSumMod_zero (q k : ℕ) [NeZero q] (a : ZMod q) :
    twistedMonomialSumMod q k a 0=completeMonomialSumMod q k a := by
  simp [twistedMonomialSumMod,completeMonomialSumMod]

theorem rationalWeightedSum_main_remainder (q k : ℕ) [NeZero q] (a : ZMod q)
    (A : Finset ℕ) (w : ℕ → ℂ) (I : ℂ) :
    rationalWeightedSum q k a A w-(completeMonomialSumMod q k a/q)*I =
      (completeMonomialSumMod q k a/q)*((∑ n∈A,w n)-I)+
      (q : ℂ)⁻¹*∑ b∈(Finset.univ : Finset (ZMod q)).erase 0,
        twistedMonomialSumMod q k a b*completedLinearSum q A w b := by
  rw [rationalWeightedSum_completion,← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q)),
    completedLinearSum_zero,twistedMonomialSumMod_zero]
  ring

theorem rationalWeightedSum_main_error_le (q k : ℕ) [NeZero q] (a : ZMod q)
    (A : Finset ℕ) (w : ℕ → ℂ) (I : ℂ) :
    ‖rationalWeightedSum q k a A w-(completeMonomialSumMod q k a/q)*I‖ ≤
      (‖completeMonomialSumMod q k a‖/q)*‖(∑ n∈A,w n)-I‖+
      (q : ℝ)⁻¹*∑ b∈(Finset.univ : Finset (ZMod q)).erase 0,
        ‖twistedMonomialSumMod q k a b‖*‖completedLinearSum q A w b‖ := by
  rw [rationalWeightedSum_main_remainder]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_div,Complex.norm_natCast,norm_mul,norm_inv,Complex.norm_natCast]
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [norm_mul] using norm_sum_le
    ((Finset.univ : Finset (ZMod q)).erase 0)
    (fun b => twistedMonomialSumMod q k a b*completedLinearSum q A w b)

theorem ordinaryWeyl_eq_rationalWeightedSum (q k : ℕ) [NeZero q]
    (a : ℤ) (P β : ℝ) :
    ordinaryWeyl k P ((a : ℝ)/q+β)=
      rationalWeightedSum q k (a : ZMod q) (ordinaryNumbers P)
        (fun n => e (β*(n : ℝ)^k)) := by
  unfold ordinaryWeyl rationalWeightedSum
  apply Finset.sum_congr rfl
  intro n _
  rw [phase_eq_e,stdAddChar_monomial_nat,← e_add]
  congr 1
  ring

/-- Exact completion with the actual singular-integral model. The two
remaining errors are an unweighted quadrature error and nonzero linear
frequencies; no cancellation estimate is included as an assumption. -/
theorem ordinaryWeyl_major_error_decomposition (q k : ℕ) [NeZero q]
    (a : ℤ) (P β : ℝ) :
    ordinaryWeyl k P ((a : ℝ)/q+β)-
        (completeMonomialSumMod q k (a : ZMod q)/q)*monomialIntegral k P β =
      (completeMonomialSumMod q k (a : ZMod q)/q)*
        ((∑ n∈ordinaryNumbers P,e (β*(n : ℝ)^k))-monomialIntegral k P β)+
      (q : ℂ)⁻¹*∑ b∈(Finset.univ : Finset (ZMod q)).erase 0,
        twistedMonomialSumMod q k (a : ZMod q) b*
          completedLinearSum q (ordinaryNumbers P) (fun n => e (β*(n : ℝ)^k)) b := by
  rw [ordinaryWeyl_eq_rationalWeightedSum]
  exact rationalWeightedSum_main_remainder q k (a : ZMod q) _ _ _

/-- The finite geometric bound for a nonzero Fourier frequency. -/
theorem completedLinearSum_geometric_bound (q N : ℕ) [NeZero q]
    (b : ZMod q) (hb : b≠0) :
    ‖completedLinearSum q (Finset.range N) (fun _ => 1) b‖ ≤
      2/‖ZMod.stdAddChar (-b)-1‖ := by
  have hz : ZMod.stdAddChar (-b)≠(1 : ℂ) := by
    intro h
    apply hb
    have hn : -b=0 := ZMod.injective_stdAddChar (by simpa only [AddChar.map_zero_eq_one] using h)
    simpa only [neg_eq_zero] using hn
  have hpower (n : ℕ) : ZMod.stdAddChar (-b*(n : ZMod q))=ZMod.stdAddChar (-b)^n := by
    simpa only [nsmul_eq_mul,mul_comm] using ZMod.stdAddChar.map_nsmul_eq_pow n (-b)
  unfold completedLinearSum
  simp only [one_mul,hpower]
  rw [geom_sum_eq hz,norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply (norm_sub_le _ _).trans
  norm_num [norm_pow,ZMod.stdAddChar_apply]

#print axioms ordinaryWeyl_major_error_decomposition
#print axioms completedLinearSum_geometric_bound

end Waring.EndgameCompletion
