import Waring.SeedCompletionCurveNoLine

/-! # Common parity excludes positive-slope affine identities -/

noncomputable section
open Polynomial
open scoped Polynomial Polynomial.Bivariate
namespace Waring.SeedCompletionCurveTranslation

theorem parity_affine_identity_eq {f g : ℝ[X]} {a b x y σ : ℝ}
    (hf : 0<f.natDegree) (hdegree : f.natDegree=g.natDegree)
    (hleading : f.leadingCoeff=g.leadingCoeff) (ha : 0<a) (hb : 0<b)
    (hσ : σ^2=1) (hparf : ∀ t : ℝ,f.eval (-t)=σ*f.eval t)
    (hparg : ∀ t : ℝ,g.eval (-t)=σ*g.eval t)
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
      _ = σ*f.eval (-(t+c)) := by rw [hparf,← mul_assoc,← pow_two,hσ,one_mul]
      _ = σ*g.eval (-(t+c)+c) := by rw [hshift]
      _ = σ*g.eval (-t) := by congr 2; ring
      _ = g.eval t := by rw [hparg,← mul_assoc,← pow_two,hσ,one_mul]
  have hc : c=0 := by
    by_contra hc
    have hg := polynomial_eq_constant_of_periodic (mul_ne_zero (by norm_num) hc) hperiod
    have hdeg := congrArg natDegree hg
    rw [natDegree_C] at hdeg
    omega
  apply Polynomial.funext
  intro t
  simpa only [hc,add_zero] using hshift t

theorem translate_ne_of_divides_separated_parity {p : ℝ[X][Y]} {f g : ℝ[X]}
    {a b x y σ : ℝ} (hf : 0<f.natDegree) (hdegree : f.natDegree=g.natDegree)
    (hleading : f.leadingCoeff=g.leadingCoeff) (ha : 0<a) (hb : 0<b)
    (hσ : σ^2=1) (hparf : ∀ t : ℝ,f.eval (-t)=σ*f.eval t)
    (hparg : ∀ t : ℝ,g.eval (-t)=σ*g.eval t)
    (hne : f≠g) (hdiv : p∣separatedCurve f g) (hzero : p.evalEval x y=0) :
    translate p a b≠p := by
  intro hinv
  apply hne
  apply parity_affine_identity_eq hf hdegree hleading ha hb hσ hparf hparg
  intro t
  have hh := invariant_divisor_line_zeros hdiv hinv hzero t
  rw [evalEval_separatedCurve,sub_eq_zero] at hh
  exact hh

#print axioms parity_affine_identity_eq
#print axioms translate_ne_of_divides_separated_parity
end Waring.SeedCompletionCurveTranslation
