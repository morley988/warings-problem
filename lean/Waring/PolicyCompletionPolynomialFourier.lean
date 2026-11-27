import Waring.PolicyCompletionPolynomialComplete
import Waring.PolicyCompletionPolynomialQuadrature
import Waring.EndgameCompletionHarmonic

/-!
# Exact Fourier completion for the auxiliary polynomial phase

Every completion frequency is retained. The actual zero-frequency sum is
compared with its actual integral using the proved uniform quadrature,
and the nonzero frequencies use the polynomial first-derivative estimate.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionPolynomialFourier
open Polynomial QuadraticModulation EndgameCompletion
open PolicyCompletionPolynomialStationary PolicyCompletionPolynomialResidues
open PolicyCompletionPolynomialDiscrete PolicyCompletionPolynomialCalculus
open PolicyCompletionPolynomialQuadrature

def twistedPolynomialSum (q : ℕ) [NeZero q] (f : Polynomial ℤ) (b : ZMod q) : ℂ :=
  ∑ x : ZMod q, ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod q))).eval x+b*x)

theorem twistedPolynomialSum_eq_integerPolynomialSum (q : ℕ) [NeZero q]
    (f : Polynomial ℤ) (b : ZMod q) :
    twistedPolynomialSum q f b = integerPolynomialSum q (f+C (b.val:ℤ)*X) := by
  unfold twistedPolynomialSum integerPolynomialSum completePolynomialSum
  apply Finset.sum_congr rfl
  intro x _
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.map_natCast, Polynomial.eval_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem polynomial_fourier_inversion (q : ℕ) [NeZero q] (f : Polynomial ℤ) (y : ZMod q) :
    (∑ b : ZMod q, twistedPolynomialSum q f b*ZMod.stdAddChar (-b*y)) =
      (q:ℂ)*ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod q))).eval y) := by
  unfold twistedPolynomialSum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : ZMod q, ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod q))).eval x)*
        ∑ b : ZMod q, ZMod.stdAddChar ((x-y)*b) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = _ := by
      simp only [stdAddChar_mul_sum, sub_eq_zero]
      simp [mul_comm]

def rationalPolynomialWeightedSum (q : ℕ) [NeZero q] (f : Polynomial ℤ)
    (A : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ A, ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod q))).eval (n:ZMod q))*w n

theorem rationalPolynomialWeightedSum_completion (q : ℕ) [NeZero q] (f : Polynomial ℤ)
    (A : Finset ℕ) (w : ℕ → ℂ) :
    rationalPolynomialWeightedSum q f A w =
      (q:ℂ)⁻¹*∑ b : ZMod q, twistedPolynomialSum q f b*completedLinearSum q A w b := by
  have hq : (q:ℂ)≠0 := by exact_mod_cast (NeZero.ne q)
  apply mul_left_cancel₀ (a := (q:ℂ)) hq
  rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  unfold rationalPolynomialWeightedSum completedLinearSum
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  have hinv := polynomial_fourier_inversion q f (n:ZMod q)
  calc
    _ = ((q:ℂ)*ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod q))).eval (n:ZMod q)))*w n := by ring
    _ = (∑ b : ZMod q, twistedPolynomialSum q f b*ZMod.stdAddChar (-b*(n:ZMod q)))*w n :=
      congrArg (fun z : ℂ => z*w n) hinv.symm
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring

@[simp] theorem twistedPolynomialSum_zero (q : ℕ) [NeZero q] (f : Polynomial ℤ) :
    twistedPolynomialSum q f 0 = integerPolynomialSum q f := by
  simp [twistedPolynomialSum, integerPolynomialSum, completePolynomialSum]

theorem rationalPolynomialWeightedSum_main_remainder (q : ℕ) [NeZero q]
    (f : Polynomial ℤ) (A : Finset ℕ) (w : ℕ → ℂ) (I : ℂ) :
    rationalPolynomialWeightedSum q f A w-(integerPolynomialSum q f/q)*I =
      (integerPolynomialSum q f/q)*((∑ n ∈ A, w n)-I)+
      (q:ℂ)⁻¹*∑ b ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        twistedPolynomialSum q f b*completedLinearSum q A w b := by
  rw [rationalPolynomialWeightedSum_completion,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (0:ZMod q)),
    completedLinearSum_zero, twistedPolynomialSum_zero]
  ring

theorem rationalPolynomialWeightedSum_main_error_le (q : ℕ) [NeZero q]
    (f : Polynomial ℤ) (A : Finset ℕ) (w : ℕ → ℂ) (I : ℂ) :
    ‖rationalPolynomialWeightedSum q f A w-(integerPolynomialSum q f/q)*I‖ ≤
      (‖integerPolynomialSum q f‖/q)*‖(∑ n ∈ A, w n)-I‖+
      (q:ℝ)⁻¹*∑ b ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        ‖twistedPolynomialSum q f b‖*‖completedLinearSum q A w b‖ := by
  rw [rationalPolynomialWeightedSum_main_remainder]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_mul, norm_inv, Complex.norm_natCast]
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [norm_mul] using norm_sum_le
    ((Finset.univ : Finset (ZMod q)).erase 0)
    (fun b => twistedPolynomialSum q f b*completedLinearSum q A w b)

theorem completedLinearSum_polynomial_eq (q : ℕ) [NeZero q]
    (f : Polynomial ℝ) (P β : ℝ) (b : ZMod q) :
    completedLinearSum q (ordinaryNumbers P) (fun n => e (β*f.eval (n:ℝ))) b =
      ∑ n ∈ Finset.Icc 1 ⌊P⌋₊, e (β*f.eval (n:ℝ)-((b.val:ℝ)/q)*n) := by
  unfold completedLinearSum ordinaryNumbers
  apply Finset.sum_congr rfl
  intro n _
  have hs : ZMod.stdAddChar (-b*(n:ZMod q))=e ((-(b.val:ℝ)/q)*(n:ℝ)) := by
    simpa only [pow_one, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val] using
      stdAddChar_monomial_nat q 1 (-(b.val:ℤ)) n
  rw [hs, ← e_add]
  congr 1
  ring

theorem completedLinearSum_polynomial_bound (q : ℕ) [NeZero q]
    (f : Polynomial ℝ) (hf : NonnegativeCoefficients f) {P β : ℝ}
    (hP : 0 ≤ P) (b : ZMod q) (hb : b≠0)
    (hβ : |β| *f.derivative.eval P ≤ 1/(2*(q:ℝ))) :
    ‖completedLinearSum q (ordinaryNumbers P) (fun n => e (β*f.eval (n:ℝ))) b‖ ≤
      2+(1+Real.pi/4)*(q:ℝ)/(min b.val (q-b.val):ℕ) := by
  have hq : (0:ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hbpos : 0<b.val := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hb
    exact ZMod.val_injective _ (by simpa only [ZMod.val_zero] using hz)
  have hd : 0<min b.val (q-b.val) := lt_min hbpos (Nat.sub_pos_of_lt b.val_lt)
  have hdR : (0:ℝ)<(min b.val (q-b.val):ℕ) := by exact_mod_cast hd
  have hdist : integerDistance ((b.val:ℝ)/q)=((min b.val (q-b.val):ℕ):ℝ)/q := by
    simpa only [integerDistance, Nat.mod_eq_of_lt b.val_lt] using
      (abs_sub_round_div_natCast_eq (α := ℝ) (m := b.val) (n := q))
  have hθ : 0 < integerDistance ((b.val:ℝ)/q) := by rw [hdist]; positivity
  have hsmall : |β| *f.derivative.eval (⌊P⌋₊:ℝ) ≤ integerDistance ((b.val:ℝ)/q)/2 := by
    calc
      _ ≤ |β| *f.derivative.eval P := mul_le_mul_of_nonneg_left
        (eval_monotone _ (derivative_nonnegative f hf) (Nat.cast_nonneg _) (Nat.floor_le hP))
        (abs_nonneg _)
      _ ≤ 1/(2*(q:ℝ)) := hβ
      _ ≤ _ := by
        rw [hdist]
        have hd1 : (1:ℝ)≤(min b.val (q-b.val):ℕ) := by exact_mod_cast hd
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
        apply (le_div_iff₀ hq).mpr
        field_simp
        linarith
  rw [completedLinearSum_polynomial_eq]
  apply (norm_polynomial_positive_sum_le f hf ⌊P⌋₊ β ((b.val:ℝ)/q) hθ hsmall).trans_eq
  rw [hdist]
  field_simp

#print axioms rationalPolynomialWeightedSum_main_remainder
#print axioms completedLinearSum_polynomial_bound
end Waring.PolicyCompletionPolynomialFourier
