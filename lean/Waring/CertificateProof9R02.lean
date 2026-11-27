import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate
theorem round9_02_checked : checkRound 9 policies9 coefficient9.values round9_01.outputs round9_02 = true := by decide +kernel
#print axioms round9_02_checked
end Waring.Certificate
