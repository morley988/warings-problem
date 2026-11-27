import WaringLinear.FiniteLocalInverse
import WaringLinear.QuadraticTaylor
import Mathlib.Tactic.LinearCombination

/-! # First and second differences of the critical-value phase

On a simple branch the primal displacement and dual displacement differ
by a unit. The critical value has slope equal to minus the primal point
and its Hessian is the negative inverse of the primal Hessian. The identities
are stated over a local ring, including ramified conductor quotients.
-/
noncomputable section
namespace WaringLinear
open Polynomial IsLocalRing
variable {A : Type*} [CommRing A] [IsLocalRing A]

def criticalValue (f : A[X]) (b x : A) : A := f.eval x-b*x

theorem displacement_unit (g : A[X]) (x y : A) (hres : residue A y=residue A x)
    (hder : IsUnit (g.derivative.eval x)) :
    ∃ a : A, IsUnit a ∧ g.eval y-g.eval x=(y-x)*a := by
  refine ⟨polynomialDifference g x (y-x),simple_difference_unit g hres hder,?_⟩
  simpa only [show x+(y-x)=y by abel] using (mul_polynomialDifference g x (y-x)).symm

theorem nilpotent_primal_displacement (g : A[X]) (x y : A) (hres : residue A y=residue A x)
    (hder : IsUnit (g.derivative.eval x)) (n : ℕ) (hn : (g.eval y-g.eval x)^n=0) :
    (y-x)^n=0 := by
  obtain ⟨a,ha,he⟩ := displacement_unit g x y hres hder
  rw [he,mul_pow] at hn
  exact (ha.pow n).mul_left_inj.mp (hn.trans (zero_mul _).symm)

theorem critical_value_linear (f : A[X]) (x y : A) (hres : residue A y=residue A x)
    (hder : IsUnit (f.derivative.derivative.eval x))
    (hδ : (f.derivative.eval y-f.derivative.eval x)^2=0) :
    criticalValue f (f.derivative.eval y) y-criticalValue f (f.derivative.eval x) x =
      -(f.derivative.eval y-f.derivative.eval x)*x := by
  have ht := nilpotent_primal_displacement f.derivative x y hres hder 2 hδ
  obtain ⟨a,_,ha⟩ := displacement_unit f.derivative x y hres hder
  have he := f.eval_add_of_sq_eq_zero x (y-x) ht
  rw [show x+(y-x)=y by abel] at he
  have hz : (f.derivative.eval y-f.derivative.eval x)*(y-x)=0 := by
    rw [ha];linear_combination a*ht
  unfold criticalValue
  linear_combination he-hz

/-- A division-free identity for the Hessian of the Fourier-dual phase.
At dual displacement δ with δ³=0 its second term is −δ²/(2 f''(x))
whenever 2 is a unit. -/
theorem critical_value_quadratic (f : A[X]) (x y : A) (hres : residue A y=residue A x)
    (hder : IsUnit (f.derivative.derivative.eval x))
    (hδ : (f.derivative.eval y-f.derivative.eval x)^3=0) :
    2*f.derivative.derivative.eval x *
      (criticalValue f (f.derivative.eval y) y-criticalValue f (f.derivative.eval x) x+
        (f.derivative.eval y-f.derivative.eval x)*x) +
      (f.derivative.eval y-f.derivative.eval x)^2=0 := by
  let t := y-x
  have hy : x+t=y := by dsimp [t];abel
  have ht : t^3=0 := nilpotent_primal_displacement f.derivative x y hres hder 3 hδ
  have hf := evaluate_cubic_nilpotent_step f x t ht
  have hb := evaluate_cubic_nilpotent_step f.derivative x t ht
  rw [hy] at hf hb
  let h := (hasseDeriv 2 f).eval x
  let j := (hasseDeriv 2 f.derivative).eval x
  let b := f.derivative.eval x
  let hess := f.derivative.derivative.eval x
  have htwo : 2*h=hess := double_hasse_two f x
  change f.eval y=f.eval x+b*t+h*t^2 at hf
  change f.derivative.eval y=b+hess*t+j*t^2 at hb
  unfold criticalValue
  change 2*hess*(f.eval y-f.derivative.eval y*y-(f.eval x-b*x)+
    (f.derivative.eval y-b)*x)+(f.derivative.eval y-b)^2=0
  rw [hf,hb,←hy,←htwo]
  linear_combination (j^2*t)*ht

#print axioms critical_value_linear
#print axioms critical_value_quadratic
end WaringLinear
