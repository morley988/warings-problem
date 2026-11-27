import Waring.Certificate
import Waring.CertificateSemantics
import Waring.Endgame
import Mathlib.Tactic.NormNum

/-!
# Conditional analytic conclusions from the complete finite certificates

The named conclusions below are conditional. Their explicit premises are the
actual admissibility of the two seed tables and analytic soundness of the four
frozen policies. These premises have NOT been proved by the finite certificate.
All finite rounds, interpolation, and upward rounding are linked to the actual
smooth-moment definition. No new axiom is introduced.
-/

noncomputable section
namespace Waring.Certificate
open Waring.SmoothMoments Waring.Endgame

/-- Conditional analytic meaning of the full degree-8 certificate. -/
theorem final8_admissible_conditional
    (hseed : AdmissibleCurve 8 source8)
    (hcoefficientSeed : AdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    AdmissibleCurve 8 final8.values := by
  have hc : AdmissibleCurve 16 coefficient8.values :=
    checkedInterpolation_admissible 16 coefficientSource8 coefficient8
      coefficient8_checked hcoefficientSeed
  have h01 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    source8 round8_01 round8_01_checked hseed hc hsound
  have h02 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_01.outputs round8_02 round8_02_checked h01 hc hsound
  have h03 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_02.outputs round8_03 round8_03_checked h02 hc hsound
  have h04 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_03.outputs round8_04 round8_04_checked h03 hc hsound
  have h05 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_04.outputs round8_05 round8_05_checked h04 hc hsound
  have h06 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_05.outputs round8_06 round8_06_checked h05 hc hsound
  have h07 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_06.outputs round8_07 round8_07_checked h06 hc hsound
  have h08 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_07.outputs round8_08 round8_08_checked h07 hc hsound
  have h09 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_08.outputs round8_09 round8_09_checked h08 hc hsound
  have h10 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_09.outputs round8_10 round8_10_checked h09 hc hsound
  have h11 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_10.outputs round8_11 round8_11_checked h10 hc hsound
  have h12 := checkedRound_admissible_conditional 8 policies8 coefficient8.values
    round8_11.outputs round8_12 round8_12_checked h11 hc hsound
  exact checkedInterpolation_admissible 8 round8_12.outputs final8
    final8_interpolation_checked h12

/-- Conditional analytic meaning of the full degree-9 certificate. -/
theorem final9_admissible_conditional
    (hseed : AdmissibleCurve 9 source9)
    (hcoefficientSeed : AdmissibleCurve 18 coefficientSource9)
    (hsound : ∀ i, i < policies9.size → AnalyticPolicySound 9 policies9[i]!) :
    AdmissibleCurve 9 final9.values := by
  have hc : AdmissibleCurve 18 coefficient9.values :=
    checkedInterpolation_admissible 18 coefficientSource9 coefficient9
      coefficient9_checked hcoefficientSeed
  have h01 := checkedRound_admissible_conditional 9 policies9 coefficient9.values
    source9 round9_01 round9_01_checked hseed hc hsound
  have h02 := checkedRound_admissible_conditional 9 policies9 coefficient9.values
    round9_01.outputs round9_02 round9_02_checked h01 hc hsound
  have h03 := checkedRound_admissible_conditional 9 policies9 coefficient9.values
    round9_02.outputs round9_03 round9_03_checked h02 hc hsound
  have h04 := checkedRound_admissible_conditional 9 policies9 coefficient9.values
    round9_03.outputs round9_04 round9_04_checked h03 hc hsound
  have h05 := checkedRound_admissible_conditional 9 policies9 coefficient9.values
    round9_04.outputs round9_05 round9_05_checked h04 hc hsound
  have h06 := checkedRound_admissible_conditional 9 policies9 coefficient9.values
    round9_05.outputs round9_06 round9_06_checked h05 hc hsound
  exact checkedInterpolation_admissible 9 round9_06.outputs final9
    final9_interpolation_checked h06

/-- Exact excesses needed for the degree-8 endgame, still conditional on the
published seeds and the new analytic policy estimates. -/
theorem final8_excesses_conditional
    (hseed : AdmissibleCurve 8 source8)
    (hcoefficientSeed : AdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    AdmissibleExcess 8 32 delta8_32 ∧
    AdmissibleExcess 8 34 delta8_34 := by
  have hfinal := final8_admissible_conditional hseed hcoefficientSeed hsound
  constructor
  · have hvalue : final8.values[16]! = (24178844726003 / 1000000000000 : Q) := by
      decide +kernel
    have heq : (final8.values[16]! : ℝ) = (32 : ℝ) - 8 + delta8_32 := by
      rw [hvalue]
      norm_num [delta8_32]
    change AdmissibleExponent 8 32 ((32 : ℝ) - 8 + delta8_32)
    rw [← heq]
    exact hfinal 16 (by decide +kernel)
  · have hvalue : final8.values[17]! = (26117131705619 / 1000000000000 : Q) := by
      decide +kernel
    have heq : (final8.values[17]! : ℝ) = (34 : ℝ) - 8 + delta8_34 := by
      rw [hvalue]
      norm_num [delta8_34]
    change AdmissibleExponent 8 34 ((34 : ℝ) - 8 + delta8_34)
    rw [← heq]
    exact hfinal 17 (by decide +kernel)

/-- Exact excesses needed for the degree-9 endgame, still conditional on the
published seeds and the new analytic policy estimates. -/
theorem final9_excesses_conditional
    (hseed : AdmissibleCurve 9 source9)
    (hcoefficientSeed : AdmissibleCurve 18 coefficientSource9)
    (hsound : ∀ i, i < policies9.size → AnalyticPolicySound 9 policies9[i]!) :
    AdmissibleExcess 9 38 delta9_38 ∧
    AdmissibleExcess 9 40 delta9_40 := by
  have hfinal := final9_admissible_conditional hseed hcoefficientSeed hsound
  constructor
  · have hvalue : final9.values[19]! = (29185097318519 / 1000000000000 : Q) := by
      decide +kernel
    have heq : (final9.values[19]! : ℝ) = (38 : ℝ) - 9 + delta9_38 := by
      rw [hvalue]
      norm_num [delta9_38]
    change AdmissibleExponent 9 38 ((38 : ℝ) - 9 + delta9_38)
    rw [← heq]
    exact hfinal 19 (by decide +kernel)
  · have hvalue : final9.values[20]! = (31135472843760 / 1000000000000 : Q) := by
      decide +kernel
    have heq : (final9.values[20]! : ℝ) = (40 : ℝ) - 9 + delta9_40 := by
      rw [hvalue]
      norm_num [delta9_40]
    change AdmissibleExponent 9 40 ((40 : ℝ) - 9 + delta9_40)
    rw [← heq]
    exact hfinal 20 (by decide +kernel)

#print axioms final8_admissible_conditional
#print axioms final9_admissible_conditional
#print axioms final8_excesses_conditional
#print axioms final9_excesses_conditional

end Waring.Certificate
