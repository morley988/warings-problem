import Waring.CertificateHeight
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate

theorem round8_01_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_01 := by decide +kernel

theorem round8_02_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_02 := by decide +kernel

theorem round8_03_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_03 := by decide +kernel

theorem round8_04_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_04 := by decide +kernel

theorem round8_05_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_05 := by decide +kernel

theorem round8_06_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_06 := by decide +kernel

theorem round8_07_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_07 := by decide +kernel

theorem round8_08_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_08 := by decide +kernel

theorem round8_09_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_09 := by decide +kernel

theorem round8_10_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_10 := by decide +kernel

theorem round8_11_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_11 := by decide +kernel

theorem round8_12_height_association :
    RoundHeightAssociation 8 policies8 coefficient8.values round8_12 := by decide +kernel

theorem round9_01_height_association :
    RoundHeightAssociation 9 policies9 coefficient9.values round9_01 := by decide +kernel

theorem round9_02_height_association :
    RoundHeightAssociation 9 policies9 coefficient9.values round9_02 := by decide +kernel

theorem round9_03_height_association :
    RoundHeightAssociation 9 policies9 coefficient9.values round9_03 := by decide +kernel

theorem round9_04_height_association :
    RoundHeightAssociation 9 policies9 coefficient9.values round9_04 := by decide +kernel

theorem round9_05_height_association :
    RoundHeightAssociation 9 policies9 coefficient9.values round9_05 := by decide +kernel

theorem round9_06_height_association :
    RoundHeightAssociation 9 policies9 coefficient9.values round9_06 := by decide +kernel

#print axioms round8_12_height_association
#print axioms round9_06_height_association
end Waring.Certificate
