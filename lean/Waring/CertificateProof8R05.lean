import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round8_05_checked : checkRound 8 policies8 coefficient8.values round8_04.outputs round8_05 = true := by decide +kernel
#print axioms round8_05_checked
end Waring.Certificate
