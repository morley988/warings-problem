import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round8_11_checked : checkRound 8 policies8 coefficient8.values round8_10.outputs round8_11 = true := by decide +kernel
#print axioms round8_11_checked
end Waring.Certificate
