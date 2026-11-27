import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round8_12_checked : checkRound 8 policies8 coefficient8.values round8_11.outputs round8_12 = true := by decide +kernel
#print axioms round8_12_checked
end Waring.Certificate
