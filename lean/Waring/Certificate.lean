import Waring.CertificateSoundness
import Waring.CertificateGuards
import Waring.CertificateFinal
import Waring.CertificateProof8R01
import Waring.CertificateProof8R02
import Waring.CertificateProof8R03
import Waring.CertificateProof8R04
import Waring.CertificateProof8R05
import Waring.CertificateProof8R06
import Waring.CertificateProof8R07
import Waring.CertificateProof8R08
import Waring.CertificateProof8R09
import Waring.CertificateProof8R10
import Waring.CertificateProof8R11
import Waring.CertificateProof8R12
import Waring.CertificateProof9R01
import Waring.CertificateProof9R02
import Waring.CertificateProof9R03
import Waring.CertificateProof9R04
import Waring.CertificateProof9R05
import Waring.CertificateProof9R06

namespace Waring.Certificate

/-- Complete finite rational audit for degree 8. No analytic admissibility claim. -/
def FiniteCertificate8 : Prop :=
  checkInterpolation coefficientSource8 coefficient8 = true ∧
  checkRound 8 policies8 coefficient8.values source8 round8_01 = true ∧
  checkRound 8 policies8 coefficient8.values round8_01.outputs round8_02 = true ∧
  checkRound 8 policies8 coefficient8.values round8_02.outputs round8_03 = true ∧
  checkRound 8 policies8 coefficient8.values round8_03.outputs round8_04 = true ∧
  checkRound 8 policies8 coefficient8.values round8_04.outputs round8_05 = true ∧
  checkRound 8 policies8 coefficient8.values round8_05.outputs round8_06 = true ∧
  checkRound 8 policies8 coefficient8.values round8_06.outputs round8_07 = true ∧
  checkRound 8 policies8 coefficient8.values round8_07.outputs round8_08 = true ∧
  checkRound 8 policies8 coefficient8.values round8_08.outputs round8_09 = true ∧
  checkRound 8 policies8 coefficient8.values round8_09.outputs round8_10 = true ∧
  checkRound 8 policies8 coefficient8.values round8_10.outputs round8_11 = true ∧
  checkRound 8 policies8 coefficient8.values round8_11.outputs round8_12 = true ∧
  checkInterpolation round8_12.outputs final8 = true
theorem finite_certificate8 : FiniteCertificate8 :=
  ⟨coefficient8_checked, round8_01_checked, round8_02_checked, round8_03_checked, round8_04_checked, round8_05_checked, round8_06_checked, round8_07_checked, round8_08_checked, round8_09_checked, round8_10_checked, round8_11_checked, round8_12_checked, final8_interpolation_checked⟩

/-- Complete finite rational audit for degree 9. No analytic admissibility claim. -/
def FiniteCertificate9 : Prop :=
  checkInterpolation coefficientSource9 coefficient9 = true ∧
  checkRound 9 policies9 coefficient9.values source9 round9_01 = true ∧
  checkRound 9 policies9 coefficient9.values round9_01.outputs round9_02 = true ∧
  checkRound 9 policies9 coefficient9.values round9_02.outputs round9_03 = true ∧
  checkRound 9 policies9 coefficient9.values round9_03.outputs round9_04 = true ∧
  checkRound 9 policies9 coefficient9.values round9_04.outputs round9_05 = true ∧
  checkRound 9 policies9 coefficient9.values round9_05.outputs round9_06 = true ∧
  checkInterpolation round9_06.outputs final9 = true
theorem finite_certificate9 : FiniteCertificate9 :=
  ⟨coefficient9_checked, round9_01_checked, round9_02_checked, round9_03_checked, round9_04_checked, round9_05_checked, round9_06_checked, final9_interpolation_checked⟩

theorem finite_certificates_checked : FiniteCertificate8 ∧ FiniteCertificate9 :=
  ⟨finite_certificate8, finite_certificate9⟩

def AllPolicyRanges : Prop :=
  PolicyAnalyticGuards 8 policies8[0]! ∧
  PolicyAnalyticGuards 8 policies8[1]! ∧
  PolicyAnalyticGuards 8 policies8[2]! ∧
  PolicyAnalyticGuards 8 policies8[3]! ∧
  PolicyAnalyticGuards 9 policies9[0]! ∧
  PolicyAnalyticGuards 9 policies9[1]! ∧
  PolicyAnalyticGuards 9 policies9[2]! ∧
  PolicyAnalyticGuards 9 policies9[3]!

theorem all_policy_ranges : AllPolicyRanges :=
  ⟨policy8_0_guards, policy8_1_guards, policy8_2_guards, policy8_3_guards, policy9_0_guards, policy9_1_guards, policy9_2_guards, policy9_3_guards⟩

theorem all_finite_checks : FiniteCertificate8 ∧ FiniteCertificate9 ∧ AllPolicyRanges :=
  ⟨finite_certificate8, finite_certificate9, all_policy_ranges⟩

#print axioms all_finite_checks
#print axioms finite_certificate8
#print axioms finite_certificate9
#print axioms finite_certificates_checked
end Waring.Certificate
