import Waring.SeedCompletionHigher18SimpleSeedsC21

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

theorem degree18_half_9 : AdmissibleExponent 18 18 (49666190250643/5000000000000 : ℝ) := half_9_21

theorem source18_entry_9 : AdmissibleExponent 18 18 (Certificate.coefficientSource9[9]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_9
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_9

theorem degree18_half_10 : AdmissibleExponent 18 20 (4487439529203/400000000000 : ℝ) := half_10_21

theorem source18_entry_10 : AdmissibleExponent 18 20 (Certificate.coefficientSource9[10]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_10
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_10

theorem degree18_half_11 : AdmissibleExponent 18 22 (125388987919393/10000000000000 : ℝ) := half_11_21

theorem source18_entry_11 : AdmissibleExponent 18 22 (Certificate.coefficientSource9[11]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_11
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_11

theorem degree18_half_12 : AdmissibleExponent 18 24 (34734087923671/2500000000000 : ℝ) := half_12_21

theorem source18_entry_12 : AdmissibleExponent 18 24 (Certificate.coefficientSource9[12]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_12
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_12

theorem degree18_half_13 : AdmissibleExponent 18 26 (152823304157929/10000000000000 : ℝ) := half_13_21

theorem source18_entry_13 : AdmissibleExponent 18 26 (Certificate.coefficientSource9[13]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_13
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_13

theorem degree18_half_14 : AdmissibleExponent 18 28 (83524965758289/5000000000000 : ℝ) := half_14_21

theorem source18_entry_14 : AdmissibleExponent 18 28 (Certificate.coefficientSource9[14]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_14
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_14

theorem degree18_half_15 : AdmissibleExponent 18 30 (36321804174739/2000000000000 : ℝ) := half_15_21

theorem source18_entry_15 : AdmissibleExponent 18 30 (Certificate.coefficientSource9[15]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_15
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_15

theorem degree18_half_16 : AdmissibleExponent 18 32 (196497247557249/10000000000000 : ℝ) := half_16_21

theorem source18_entry_16 : AdmissibleExponent 18 32 (Certificate.coefficientSource9[16]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_16
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_16

theorem degree18_half_17 : AdmissibleExponent 18 34 (105853452759601/5000000000000 : ℝ) := half_17_21

theorem source18_entry_17 : AdmissibleExponent 18 34 (Certificate.coefficientSource9[17]! : ℝ) := by
  apply admissibleExponent_mono degree18_half_17
  norm_num [Certificate.coefficientSource9,Certificate.Q]

#print axioms source18_entry_17


end Waring.SeedCompletionHigher18SimpleSeeds
