import Waring.FiniteFieldMordellMoment
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # The actual affine orbit and its two highest coefficients -/

noncomputable section
open Polynomial
open scoped BigOperators Polynomial
namespace Waring.FiniteFieldMordell

section Field
variable {K : Type*} [Field K]

def affinePolynomial (f : K[X]) (u v : K) : K[X] :=
  f.comp (C u*X+C v)-C (f.eval v)

def affineCoefficients (f : K[X]) (d : ℕ) (u v : K) : Fin d → K :=
  fun j => (affinePolynomial f u v).coeff (j.val+1)

theorem affine_comp_factor (f : K[X]) (u v : K) :
    f.comp (C u*X+C v)=(taylor v f).comp (C u*X) := by
  rw [taylor_apply,comp_assoc,add_comp,X_comp,C_comp]

theorem taylor_penultimate_coeff (f : K[X]) (hf : 1 ≤ f.natDegree) (v : K) :
    (taylor v f).coeff (f.natDegree-1)=
      (f.natDegree : K)*f.leadingCoeff*v+f.coeff (f.natDegree-1) := by
  have hd : (hasseDeriv (f.natDegree-1) f).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le f _).trans (by omega)
  have he := eq_X_add_C_of_natDegree_le_one hd
  have hn : 1+(f.natDegree-1)=f.natDegree := by omega
  rw [taylor_coeff,he,eval_add,eval_mul,eval_C,eval_X,eval_C]
  simp only [hasseDeriv_coeff,hn,zero_add,Nat.choose_symm hf,Nat.choose_one_right,
    Nat.choose_self,Nat.cast_one,one_mul,coeff_natDegree]

theorem affinePolynomial_coeff_top (f : K[X]) (hf : 1 ≤ f.natDegree) (u v : K) :
    (affinePolynomial f u v).coeff f.natDegree=f.leadingCoeff*u^f.natDegree := by
  rw [affinePolynomial,coeff_sub,coeff_C]
  simp only [show f.natDegree ≠ 0 by omega,ite_false,sub_zero]
  rw [affine_comp_factor,comp_C_mul_X_coeff,coeff_taylor_natDegree]

theorem affinePolynomial_coeff_penultimate (f : K[X]) (hf : 2 ≤ f.natDegree) (u v : K) :
    (affinePolynomial f u v).coeff (f.natDegree-1)=
      ((f.natDegree : K)*f.leadingCoeff*v+f.coeff (f.natDegree-1))*u^(f.natDegree-1) := by
  rw [affinePolynomial,coeff_sub,coeff_C]
  simp only [show f.natDegree-1 ≠ 0 by omega,ite_false,sub_zero]
  rw [affine_comp_factor,comp_C_mul_X_coeff,taylor_penultimate_coeff f (by omega)]

theorem affinePolynomial_natDegree (f : K[X]) {u : K} (hu : u ≠ 0) (v : K) :
    (affinePolynomial f u v).natDegree=f.natDegree := by
  rw [affinePolynomial,natDegree_sub_C,natDegree_comp,natDegree_linear hu,mul_one]

theorem affinePolynomial_coeff_zero (f : K[X]) (u v : K) :
    (affinePolynomial f u v).coeff 0=0 := by
  simp [affinePolynomial,coeff_zero_eq_eval_zero]

theorem affineCoefficients_translation_injective (f : K[X]) (hf : 2 ≤ f.natDegree)
    (hchar : (f.natDegree : K) ≠ 0) {u : K} (hu : u ≠ 0) :
    Function.Injective (affineCoefficients f f.natDegree u) := by
  intro v w hvw
  have hh := congrFun hvw (⟨f.natDegree-2,by omega⟩ : Fin f.natDegree)
  simp only [affineCoefficients,show f.natDegree-2+1=f.natDegree-1 by omega,
    affinePolynomial_coeff_penultimate f hf] at hh
  have hh' := mul_right_cancel₀ (pow_ne_zero (f.natDegree-1) hu) hh
  have hh'' := add_right_cancel hh'
  exact mul_left_cancel₀
    (mul_ne_zero hchar (leadingCoeff_ne_zero.mpr
      (ne_zero_of_natDegree_gt (show 0 < f.natDegree by omega)))) hh''

end Field

#print axioms affineCoefficients_translation_injective
end Waring.FiniteFieldMordell
