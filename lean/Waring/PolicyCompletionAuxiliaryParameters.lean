import Waring.PolicyCompletionAuxiliarySource

/-! # Exact interpolation weights of the frozen degree-eight auxiliary policy -/
noncomputable section
namespace Waring.PolicyCompletionAuxiliaryParameters
open Certificate PolicyCompletionMajorPowerRanges PolicyCompletionAuxiliarySource

theorem frozen_half_order : terminalHalfOrder policies8[0]! =8 := by decide +kernel

theorem frozen_full_order : terminalFullOrder policies8[0]! =20 := by decide +kernel

theorem frozen_auxiliary_order : policies8[0]!.auxiliaryOrder=some 20 := by decide +kernel

theorem frozen_weight : terminalWeightReal policies8[0]! =(4/5:ℝ) := by
  unfold terminalWeightReal
  rw [frozen_auxiliary_order,frozen_half_order,frozen_full_order]
  norm_num

theorem frozen_parameters (curve : Curve) :
    ((terminalParameters 8 curve policies8[0]!).base:ℝ)=
      (4/5:ℝ)*(amplitude 8 (phiReal policies8[0]!)+12*(1-total (phiReal policies8[0]!))) ∧
    ((terminalParameters 8 curve policies8[0]!).slope:ℝ)=
      (4/5:ℝ)*(2*((delta 8 curve 20).getD 0:ℝ)/8) ∧
    ((terminalParameters 8 curve policies8[0]!).scale:ℝ)=(3/5:ℝ) := by
  have hj : policies8[0]!.phi.size=6 := by decide +kernel
  rw [terminalParameters_base_cast,terminalParameters_slope_cast,terminalParameters_scale_cast,
    frozen_weight,frozen_full_order]
  constructor
  · norm_num <;> ring
  constructor
  · norm_num <;> ring
  · rw [hj]
    norm_num

#print axioms frozen_parameters
end Waring.PolicyCompletionAuxiliaryParameters
