import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate

theorem coefficient8_checked : checkInterpolation coefficientSource8 coefficient8 = true := by decide +kernel
theorem coefficient9_checked : checkInterpolation coefficientSource9 coefficient9 = true := by decide +kernel
theorem final8_interpolation_checked : checkInterpolation round8_12.outputs final8 = true := by decide +kernel
theorem final9_interpolation_checked : checkInterpolation round9_06.outputs final9 = true := by decide +kernel

def outputDelta8 (order : Nat) : Q := (delta 8 final8.values order).getD 0
def outputDelta9 (order : Nat) : Q := (delta 9 final9.values order).getD 0

theorem final8_delta32 : delta 8 final8.values 32 = some (178844726003 / 1000000000000) := by decide +kernel
theorem final8_delta34 : delta 8 final8.values 34 = some (117131705619 / 1000000000000) := by decide +kernel
theorem final9_delta38 : delta 9 final9.values 38 = some (185097318519 / 1000000000000) := by decide +kernel
theorem final9_delta40 : delta 9 final9.values 40 = some (135472843760 / 1000000000000) := by decide +kernel

theorem final8_criterion : outputDelta8 32 + 7*outputDelta8 34 - 1 = -154166833 / 125000000000 := by decide +kernel
theorem final9_criterion : 5*outputDelta9 38 + 74*outputDelta9 40 - 11 = -9904593833 / 200000000000 := by decide +kernel

theorem final8_coarse_pair : outputDelta8 32 ≤ 1789/10000 ∧ outputDelta8 34 ≤ 11721/100000 := by decide +kernel
theorem final9_coarse_pair : outputDelta9 38 ≤ 1851/10000 ∧ outputDelta9 40 ≤ 271/2000 := by decide +kernel

theorem final8_criterion_negative : outputDelta8 32 + 7*outputDelta8 34 - 1 < 0 := by decide +kernel
theorem final9_criterion_negative : 5*outputDelta9 38 + 74*outputDelta9 40 - 11 < 0 := by decide +kernel

theorem final8_minor_saving : 7/100000 < -(outputDelta8 32 + 7*outputDelta8 34 - 1)/9 := by decide +kernel
theorem final9_minor_saving : 1/2000 < -(5*outputDelta9 38 + 74*outputDelta9 40 - 11)/90 := by decide +kernel

#print axioms final8_delta32
#print axioms final9_delta40
#print axioms final8_criterion
#print axioms final9_criterion
end Waring.Certificate
