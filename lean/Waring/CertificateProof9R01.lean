import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round9_01_checked : checkRound 9 policies9 coefficient9.values source9 round9_01 = true := by decide +kernel
#print axioms round9_01_checked
end Waring.Certificate
