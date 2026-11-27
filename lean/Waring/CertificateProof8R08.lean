import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round8_08_checked : checkRound 8 policies8 coefficient8.values round8_07.outputs round8_08 = true := by decide +kernel
#print axioms round8_08_checked
end Waring.Certificate
