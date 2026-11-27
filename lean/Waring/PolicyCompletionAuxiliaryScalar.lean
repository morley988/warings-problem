import Waring.PolicyCompletionWeightedHeight

/-! # Exact scalar power identities for the auxiliary terminal -/
noncomputable section
open scoped ENNReal
namespace Waring.PolicyCompletionAuxiliaryScalar

theorem auxiliary_powered_pointwise {X C P a b δ S : ℝ}
    (hP : 0<P) (hC : 0≤C) (hX : 0≤X) (hb : X≤C*P^(a+δ-S)) :
    (ENNReal.ofReal X)^(3/5:ℝ)≤
      ENNReal.ofReal (C^(3/5:ℝ)*P^((3/5:ℝ)*δ-(1/5:ℝ)*a-(4/5:ℝ)*b))*
      ENNReal.ofReal (P^((4/5:ℝ)*(a+b)-(3/5:ℝ)*S)) := by
  have hh:=ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hb) (by norm_num : (0:ℝ)≤3/5)
  apply hh.trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ←ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow hC (Real.rpow_nonneg hP.le _),←Real.rpow_mul hP.le,
    mul_assoc,←Real.rpow_add hP]
  congr 2
  ring

theorem auxiliary_inner_scalar {C G T P a b δ E : ℝ}
    (hP : 0<P) (hC : 0<C) (hG : 0<G) (hT : 0<T) :
    (ENNReal.ofReal (C^(3/5:ℝ)*P^((3/5:ℝ)*δ-(1/5:ℝ)*a-(4/5:ℝ)*b)))^(5/4:ℝ)*
      ENNReal.ofReal (G*P^(b+δ))*ENNReal.ofReal (T*P^(E*(5/4:ℝ)+δ))=
      ENNReal.ofReal ((C^(3/4:ℝ)*G*T)*P^((5/4:ℝ)*E-a/4+(11/4:ℝ)*δ)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  repeat' rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hP.le _),
    ←Real.rpow_mul hC.le,←Real.rpow_mul hP.le]
  norm_num only [show (3/5:ℝ)*(5/4)=3/4 by norm_num]
  calc
    _ = (C^(3/4:ℝ)*G*T)*(P^(((3/5:ℝ)*δ-(1/5:ℝ)*a-(4/5:ℝ)*b)*(5/4:ℝ))*
      P^(b+δ)*P^(E*(5/4:ℝ)+δ)) := by ring
    _ = _ := by rw [←Real.rpow_add hP,←Real.rpow_add hP]; congr 2; ring

theorem auxiliary_outer_scalar {L J P a δ E : ℝ}
    (hP : 0<P) (hL : 0<L) (hJ : 0<J) :
    (L*P^(a+δ))^(1/5:ℝ)*(J*P^((5/4:ℝ)*E-a/4+(11/4:ℝ)*δ))^(4/5:ℝ)=
      (L^(1/5:ℝ)*J^(4/5:ℝ))*P^(E+(12/5:ℝ)*δ) := by
  rw [Real.mul_rpow hL.le (Real.rpow_nonneg hP.le _),
    Real.mul_rpow hJ.le (Real.rpow_nonneg hP.le _),←Real.rpow_mul hP.le,←Real.rpow_mul hP.le]
  calc
    _ = (L^(1/5:ℝ)*J^(4/5:ℝ))*(P^((a+δ)*(1/5:ℝ))*
      P^(((5/4:ℝ)*E-a/4+(11/4:ℝ)*δ)*(4/5:ℝ))) := by ring
    _ = _ := by rw [←Real.rpow_add hP]; congr 2; ring

#print axioms auxiliary_powered_pointwise
#print axioms auxiliary_inner_scalar
#print axioms auxiliary_outer_scalar
end Waring.PolicyCompletionAuxiliaryScalar
