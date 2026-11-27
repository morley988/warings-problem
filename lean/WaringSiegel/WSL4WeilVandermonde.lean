import Mathlib.LinearAlgebra.Lagrange

/-! Explicit inverse rows for the finite moment system used in Ramanujam's
small-residue construction. The coefficients are literal Lagrange coefficients;
no solvability or inverse-matrix premise is assumed. -/
noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000
variable {F : Type*} [Field F] {n : ℕ}

def inverseVandermondeRow (mu : Fin (n+1) → F) (sigma j : Fin (n+1)) : F :=
  (Lagrange.basis Finset.univ mu j).coeff sigma.val

theorem inverseVandermondeRow_formula
    (mu : Fin (n+1) → F) (sigma j : Fin (n+1)) :
    inverseVandermondeRow mu sigma j =
      (∏ i∈Finset.univ.erase j,(X-C (mu i))).coeff sigma.val /
      (∏ i∈Finset.univ.erase j,(mu j-mu i)) := by
  rw [inverseVandermondeRow,
    Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ j),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ j),coeff_C_mul]
  simp only [Lagrange.nodalWeight,Lagrange.nodal,Finset.prod_inv_distrib,div_eq_mul_inv]
  ring

theorem inverseVandermondeRow_moments
    (mu : Fin (n+1) → F) (hmu : Function.Injective mu)
    (sigma t : Fin (n+1)) :
    (∑ j,inverseVandermondeRow mu sigma j*mu j^t.val)=
      if t=sigma then 1 else 0 := by
  have hpoly : (X : F[X])^t.val=Lagrange.interpolate Finset.univ mu
      (fun j => mu j^t.val) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ hmu.injOn
    · simpa only [degree_X_pow,Finset.card_univ,Fintype.card_fin,
        Nat.cast_withBot,WithBot.coe_lt_coe] using t.isLt
    · intro i hi
      simp
  have hc := congrArg (fun f : F[X] => f.coeff sigma.val) hpoly
  simp only [Lagrange.interpolate_apply,finset_sum_coeff,coeff_C_mul] at hc
  have hd : ((X : F[X])^t.val).coeff sigma.val=if t=sigma then 1 else 0 := by
    simp only [coeff_X_pow,Fin.ext_iff,eq_comm]
  rw [hd] at hc
  simpa only [inverseVandermondeRow,mul_comm] using hc.symm

theorem inverseVandermondeRow_scaled_moments
    (mu : Fin (n+1) → F) (hmu : Function.Injective mu)
    (sigma t : Fin (n+1)) (lambda : F) :
    (∑ j,(lambda*inverseVandermondeRow mu sigma j)*mu j^t.val)=
      if t=sigma then lambda else 0 := by
  simp only [mul_assoc,← Finset.mul_sum,inverseVandermondeRow_moments mu hmu]
  split_ifs <;> simp

end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.inverseVandermondeRow_formula
#print axioms WaringSiegel.WSL4Weil.inverseVandermondeRow_moments
#print axioms WaringSiegel.WSL4Weil.inverseVandermondeRow_scaled_moments
