import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round8_03_checked : checkRound 8 policies8 coefficient8.values round8_02.outputs round8_03 = true := by decide +kernel
#print axioms round8_03_checked
end Waring.Certificate
