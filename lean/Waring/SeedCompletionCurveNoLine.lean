import Waring.SeedCompletionCurveTranslation
import Mathlib.Tactic.Linarith

/-! # Distinct even polynomials admit no positive-slope affine identity -/

noncomputable section
open Polynomial
open scoped Polynomial Polynomial.Bivariate
namespace Waring.SeedCompletionCurveTranslation

theorem affine_identity_slope_eq {f g : ℝ[X]} {a b x y : ℝ}
    (hf : 0 < f.natDegree) (hdegree : f.natDegree=g.natDegree)
    (hleading : f.leadingCoeff=g.leadingCoeff) (ha : 0 < a) (hb : 0 < b)
    (hid : ∀ t : ℝ,f.eval (a*t+x)=g.eval (b*t+y)) : a=b := by
  have hpoly : f.comp (C a*X+C x)=g.comp (C b*X+C y) := by
    apply Polynomial.funext
    intro t
    simpa only [eval_comp,eval_add,eval_mul,eval_C,eval_X] using hid t
  have he := congrArg leadingCoeff hpoly
  rw [leadingCoeff_comp (by rw [natDegree_linear ha.ne']; norm_num),
    leadingCoeff_comp (by rw [natDegree_linear hb.ne']; norm_num),
    leadingCoeff_linear ha.ne',leadingCoeff_linear hb.ne',← hleading,← hdegree] at he
  have hpow := mul_left_cancel₀ (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hf)) he
  exact (pow_left_inj₀ ha.le hb.le hf.ne').mp hpow

theorem even_affine_identity_eq {f g : ℝ[X]} {a b x y : ℝ}
    (hf : 0 < f.natDegree) (hdegree : f.natDegree=g.natDegree)
    (hleading : f.leadingCoeff=g.leadingCoeff) (ha : 0 < a) (hb : 0 < b)
    (hevenf : ∀ t : ℝ,f.eval (-t)=f.eval t) (heveng : ∀ t : ℝ,g.eval (-t)=g.eval t)
    (hid : ∀ t : ℝ,f.eval (a*t+x)=g.eval (b*t+y)) : f=g := by
  have hab := affine_identity_slope_eq hf hdegree hleading ha hb hid
  subst b
  let c := y-x
  have hshift : ∀ z : ℝ,f.eval z=g.eval (z+c) := by
    intro z
    have ht : a*((z-x)/a)+x=z := by field_simp; ring
    have ht' : a*((z-x)/a)+y=z+c := by dsimp [c]; field_simp; ring
    simpa only [ht,ht'] using hid ((z-x)/a)
  have hperiod : ∀ t : ℝ,g.eval (t+2*c)=g.eval t := by
    intro t
    calc
      _ = g.eval ((t+c)+c) := by congr 1; ring
      _ = f.eval (t+c) := (hshift _).symm
      _ = f.eval (-(t+c)) := (hevenf _).symm
      _ = g.eval (-(t+c)+c) := hshift _
      _ = g.eval (-t) := by congr 1; ring
      _ = g.eval t := heveng _
  have hc : c=0 := by
    by_contra hc
    have hg := polynomial_eq_constant_of_periodic (mul_ne_zero (by norm_num) hc) hperiod
    have hdeg := congrArg natDegree hg
    rw [natDegree_C] at hdeg
    omega
  apply Polynomial.funext
  intro t
  simpa only [hc,add_zero] using hshift t

def separatedCurve (f g : ℝ[X]) : ℝ[X][Y] := C f-g.map C

theorem evalEval_separatedCurve (f g : ℝ[X]) (x y : ℝ) :
    (separatedCurve f g).evalEval x y=f.eval x-g.eval y := by
  simp [separatedCurve,evalEval,eval_map,eval₂_at_apply]

/-- A factor with an actual real point cannot be fixed by a strictly
positive translation when its source curve comes from distinct even
polynomials with the same degree and leading coefficient. -/
theorem translate_ne_of_divides_separated {p : ℝ[X][Y]} {f g : ℝ[X]} {a b x y : ℝ}
    (hf : 0 < f.natDegree) (hdegree : f.natDegree=g.natDegree)
    (hleading : f.leadingCoeff=g.leadingCoeff) (ha : 0 < a) (hb : 0 < b)
    (hevenf : ∀ t : ℝ,f.eval (-t)=f.eval t) (heveng : ∀ t : ℝ,g.eval (-t)=g.eval t)
    (hne : f ≠ g) (hdiv : p ∣ separatedCurve f g) (hzero : p.evalEval x y=0) :
    translate p a b ≠ p := by
  intro hinv
  apply hne
  apply even_affine_identity_eq hf hdegree hleading ha hb hevenf heveng
  intro t
  have hh := invariant_divisor_line_zeros hdiv hinv hzero t
  rw [evalEval_separatedCurve,sub_eq_zero] at hh
  exact hh

#print axioms even_affine_identity_eq
#print axioms translate_ne_of_divides_separated
end Waring.SeedCompletionCurveTranslation
