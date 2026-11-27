import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Translation invariance forces an actual affine line of zeros

Only polynomial identities and the finite root bound are used. In the
curve application this excludes an invariant irreducible factor directly,
without a general classification theorem for plane curves.
-/

noncomputable section
open Polynomial
open scoped Polynomial Polynomial.Bivariate
namespace Waring.SeedCompletionCurveTranslation

section Ring
variable {K : Type*} [CommRing K]

def translateHom (a b : K) : K[X][Y] →+* K[X][Y] :=
  (compRingHom (X+C (C b))).comp (mapRingHom (compRingHom (X+C a)))

def translate (p : K[X][Y]) (a b : K) : K[X][Y] := translateHom a b p

theorem translate_eq_map_comp (p : K[X][Y]) (a b : K) :
    translate p a b=(p.map (eval₂RingHom C (X+C a))).comp (X+C (C b)) := rfl

theorem evalEval_translate (p : K[X][Y]) (a b x y : K) :
    (translate p a b).evalEval x y=p.evalEval (x+a) (y+b) := by
  have he : (evalEvalRingHom x y).comp (translateHom a b)=evalEvalRingHom (x+a) (y+b) := by
    ext <;> simp [translateHom,evalEval,coe_compRingHom_apply]
  exact congrArg (fun f : K[X][Y] →+* K => f p) he

def lineRestriction (p : K[X][Y]) (x y a b : K) : K[X] :=
  p.eval₂ (compRingHom (C a*X+C x)) (C b*X+C y)

theorem eval_lineRestriction (p : K[X][Y]) (x y a b t : K) :
    (lineRestriction p x y a b).eval t=p.evalEval (a*t+x) (b*t+y) := by
  have he : (evalRingHom t).comp (eval₂RingHom (compRingHom (C a*X+C x)) (C b*X+C y))=
      evalEvalRingHom (a*t+x) (b*t+y) := by
    ext <;> simp [evalEval,coe_compRingHom_apply]
  exact congrArg (fun f : K[X][Y] →+* K => f p) he

theorem invariant_nat_zeros {p : K[X][Y]} {a b x y : K}
    (hinv : translate p a b=p) (hzero : p.evalEval x y=0) (n : ℕ) :
    p.evalEval (a*(n : K)+x) (b*(n : K)+y)=0 := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      have he := evalEval_translate p a b (a*(n : K)+x) (b*(n : K)+y)
      rw [hinv,ih] at he
      convert he.symm using 1 <;> push_cast <;> ring

end Ring

section Domain
variable {K : Type*} [CommRing K] [IsDomain K] [CharZero K]

theorem invariant_lineRestriction_eq_zero {p : K[X][Y]} {a b x y : K}
    (hinv : translate p a b=p) (hzero : p.evalEval x y=0) :
    lineRestriction p x y a b=0 := by
  let f := lineRestriction p x y a b
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (f := fun i : Fin (f.natDegree+1) => (i.val : K))
  · exact Nat.cast_injective.comp Fin.val_injective
  · intro i
    rw [eval_lineRestriction]
    exact invariant_nat_zeros hinv hzero i.val
  · simp [f]

theorem invariant_line_zeros {p : K[X][Y]} {a b x y : K}
    (hinv : translate p a b=p) (hzero : p.evalEval x y=0) (t : K) :
    p.evalEval (a*t+x) (b*t+y)=0 := by
  rw [← eval_lineRestriction,invariant_lineRestriction_eq_zero hinv hzero,eval_zero]

theorem invariant_divisor_line_zeros {p F : K[X][Y]} {a b x y : K}
    (hdiv : p ∣ F) (hinv : translate p a b=p) (hzero : p.evalEval x y=0) (t : K) :
    F.evalEval (a*t+x) (b*t+y)=0 := by
  obtain ⟨G,rfl⟩ := hdiv
  rw [evalEval_mul,invariant_line_zeros hinv hzero,zero_mul]

theorem polynomial_eq_constant_of_periodic {p : K[X]} {c : K} (hc : c ≠ 0)
    (hperiod : ∀ x : K,p.eval (x+c)=p.eval x) : p=C (p.eval 0) := by
  have hn : ∀ n : ℕ,p.eval (c*(n : K))=p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ,mul_add,mul_one,hperiod,ih]
  apply sub_eq_zero.mp
  let f := p-C (p.eval 0)
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (f := fun i : Fin (f.natDegree+1) => c*(i.val : K))
  · intro i j hij
    exact Fin.ext (Nat.cast_injective (mul_left_cancel₀ hc hij))
  · intro i
    simp only [eval_sub,eval_C,hn,sub_self]
  · simp [f]

end Domain

#print axioms invariant_line_zeros
#print axioms invariant_divisor_line_zeros
end Waring.SeedCompletionCurveTranslation
