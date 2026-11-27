import WaringSiegel.WSL4WeilVandermonde
import Mathlib.Algebra.Polynomial.Eval.Degree

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000
variable {F : Type*} [Field F] {n : ℕ}

/-- The inverse row extracts one monomial from every polynomial of degree at most n. -/
theorem inverseVandermonde_polynomial_projection
    (mu : Fin (n+1) → F) (hmu : Function.Injective mu) (sigma : Fin (n+1))
    (f : F[X]) (hf : f.natDegree≤n) :
    (∑ j,C (inverseVandermondeRow mu sigma j)*f.comp (C (mu j)*X))=
      C (f.coeff sigma.val)*X^sigma.val := by
  ext t
  simp only [finset_sum_coeff,coeff_C_mul,comp_C_mul_X_coeff,coeff_X_pow,mul_ite,mul_one,mul_zero]
  by_cases ht : t≤n
  · let t' : Fin (n+1) := ⟨t,by omega⟩
    have hm := inverseVandermondeRow_moments mu hmu sigma t'
    change (∑ j,inverseVandermondeRow mu sigma j*mu j^t)=
      (if t'=sigma then 1 else 0) at hm
    calc
      (∑ j,inverseVandermondeRow mu sigma j*(f.coeff t*mu j^t)) =
          f.coeff t*(∑ j,inverseVandermondeRow mu sigma j*mu j^t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ = f.coeff t*(if t'=sigma then 1 else 0) := by rw [hm]
      _ = if sigma.val=t then f.coeff sigma.val else 0 := by
        by_cases he : sigma.val=t
        · have ht' : t'=sigma := Fin.ext he.symm
          simp [ht',he]
        · have ht' : t'≠sigma := by intro h; exact he (congrArg Fin.val h).symm
          simp [ht',he]
      _ = _ := by simp only [eq_comm]
  · have hzero : f.coeff t=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hne : sigma.val≠t := by omega
    simp [hzero,hne,Ne.symm hne]

/-- Literal affine-power identity; all coefficients are explicit inverse-row entries. -/
theorem inverseVandermonde_affine_power_identity
    (mu : Fin (n+1) → F) (hmu : Function.Injective mu) (sigma : Fin (n+1))
    (x : F) :
    (∑ j,inverseVandermondeRow mu sigma j*(mu j*x+1)^n)=
      (n.choose sigma.val : F)*x^sigma.val := by
  have h := inverseVandermonde_polynomial_projection mu hmu sigma ((X+1)^n)
    (by rw [← C_1,natDegree_pow,natDegree_X_add_C,mul_one])
  have he := congrArg (fun f : F[X] => f.eval x) h
  simpa only [eval_finset_sum,eval_mul,eval_C,eval_comp,eval_pow,eval_add,
    eval_X,eval_one,coeff_X_add_one_pow] using he
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.inverseVandermonde_polynomial_projection
#print axioms WaringSiegel.WSL4Weil.inverseVandermonde_affine_power_identity
