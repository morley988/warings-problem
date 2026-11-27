import Waring.SeedCompletionEven18SecondSeeds
import Waring.SeedCompletionGeneralTerminal
import Waring.SeedCompletionNaturalChronological

/-! # Actual degree-18 higher seeds from condition(i)

Every finite stage uses the proved padded second/fourth moments,
literal full-box Holder and the actual all-depth recurrence.
LP calculations select rational witnesses only; all inequalities,
rounding and admissibility are checked by Lean. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

theorem half_9_00 : AdmissibleExponent 18 18 (50440903758261/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 7) (by norm_num : 0 < (18 : ℕ))
    SeedCompletionEven18SecondSeeds.degree18_half_8 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_10_00 : AdmissibleExponent 18 20 (115277262654493/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 8) (by norm_num : 0 < (18 : ℕ))
    half_9_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_11_00 : AdmissibleExponent 18 22 (129984081395911/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 9) (by norm_num : 0 < (18 : ℕ))
    half_10_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_12_00 : AdmissibleExponent 18 24 (28996993152561/2000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 10) (by norm_num : 0 < (18 : ℕ))
    half_11_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_13_00 : AdmissibleExponent 18 26 (160263578775983/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 11) (by norm_num : 0 < (18 : ℕ))
    half_12_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_14_00 : AdmissibleExponent 18 28 (175804491066207/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 12) (by norm_num : 0 < (18 : ℕ))
    half_13_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_15_00 : AdmissibleExponent 18 30 (95796565225709/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 13) (by norm_num : 0 < (18 : ℕ))
    half_14_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_16_00 : AdmissibleExponent 18 32 (207615734315229/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 14) (by norm_num : 0 < (18 : ℕ))
    half_15_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_17_00 : AdmissibleExponent 18 34 (4477186092621/200000000000 : ℝ) := by
  have h := endpoint_admissible (s := 15) (by norm_num : 0 < (18 : ℕ))
    half_16_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)


end Waring.SeedCompletionHigher18SimpleSeeds
