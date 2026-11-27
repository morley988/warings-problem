import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round8_01_checked : checkRound 8 policies8 coefficient8.values source8 round8_01 = true := by decide +kernel
#print axioms round8_01_checked
end Waring.Certificate
