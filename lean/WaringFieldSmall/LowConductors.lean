import WaringFieldSmall.RowProof
import WaringFieldSmall.Section00
import WaringFieldSmall.Section01
namespace WaringFieldSmall
open WaringEnvelope WaringLinear
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
private theorem checks0 : testList 11 Section00.b0.data [2,2,2,770,770,770,770,1026,1026,1027,1282]=true := by decide +kernel
private theorem checks1 : testList 12 Section00.b1.data [2,2,2,2,770,770,770,770,1026,1027,1027,1283,1283]=true := by decide +kernel
private theorem checks2 : testList 13 Section00.b2.data [2,2,2,2,770,770,770,770,3,1027,1027,1027,1283,1283]=true := by decide +kernel
private theorem checks3 : testList 14 Section00.b3.data [2,2,2,2,770,770,770,770,3,1027,1027,1027,1283,1283,1283]=true := by decide +kernel
private theorem checks4 : testList 15 Section00.b4.data [2,2,2,2,2,770,770,770,770,3,1027,1027,1027,1027,1283,1283,1283]=true := by decide +kernel
private theorem checks5 : testList 16 Section00.b5.data [2,2,2,2,2,770,770,770,770,3,3,1027,1027,1027,1027,1283,1283,1539,1539]=true := by decide +kernel
private theorem checks6 : testList 17 Section00.b6.data [2,2,2,2,2,770,770,770,770,770,3,3,1027,1027,1027,1027,1283,1283,1283,1539]=true := by decide +kernel
private theorem checks7 : testList 18 Section00.b7.data [2,2,2,2,2,770,770,770,770,770,3,3,1027,1027,1027,1027,1027,1283,1283,1283,1539]=true := by decide +kernel
private theorem checks8 : testList 19 Section01.b8.data [2,2,2,2,2,2,770,770,770,770,3,3,3,1027,1027,1027,1027,1027,1283,1283,1283,1283,1539]=true := by decide +kernel
private theorem checks9 : testList 20 Section01.b9.data [2,2,2,2,2,2,770,770,770,770,3,3,3,3,1027,1027,1027,1027,1027,1283,1283,1283,1539,1539,1539]=true := by decide +kernel
theorem low_conductors (k : Nat) (hl : 11≤k) (hh : k≤20) :
    ∃ band, band.lo≤k ∧ k≤band.hi ∧ band.good ∧ RowCoverage (fun b => b=band) k := by
  by_cases e : k=11
  · subst k
    refine ⟨Section00.b0,by decide,by decide,Section00.b0_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 11) (by decide) checks0 u hu
  by_cases e : k=12
  · subst k
    refine ⟨Section00.b1,by decide,by decide,Section00.b1_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 12) (by decide) checks1 u hu
  by_cases e : k=13
  · subst k
    refine ⟨Section00.b2,by decide,by decide,Section00.b2_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 13) (by decide) checks2 u hu
  by_cases e : k=14
  · subst k
    refine ⟨Section00.b3,by decide,by decide,Section00.b3_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 14) (by decide) checks3 u hu
  by_cases e : k=15
  · subst k
    refine ⟨Section00.b4,by decide,by decide,Section00.b4_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 15) (by decide) checks4 u hu
  by_cases e : k=16
  · subst k
    refine ⟨Section00.b5,by decide,by decide,Section00.b5_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 16) (by decide) checks5 u hu
  by_cases e : k=17
  · subst k
    refine ⟨Section00.b6,by decide,by decide,Section00.b6_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 17) (by decide) checks6 u hu
  by_cases e : k=18
  · subst k
    refine ⟨Section00.b7,by decide,by decide,Section00.b7_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 18) (by decide) checks7 u hu
  by_cases e : k=19
  · subst k
    refine ⟨Section01.b8,by decide,by decide,Section01.b8_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 19) (by decide) checks8 u hu
  by_cases e : k=20
  · subst k
    refine ⟨Section01.b9,by decide,by decide,Section01.b9_ok,?_⟩
    intro b he _ _ u hu;subst b
    exact testList_coverage (Nat.le_refl 20) (by decide) checks9 u hu
  omega
variable {K : Type*} [Field K] [NumberField K]
theorem degree_eleven_through_twenty (W : ℝ → TraceSumFamily K) (k : ℕ) (hl : 11≤k) (hh : k≤20)
    (count : DifferencingCounts W k)
    (step : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ 0<a ∧ cutoffAdmissible W k r x ∧ 0≤x ∧
      (k:ℝ)*x<((a:ℝ)-1)*(1/(15*k)) ∧ 2*k<r+a ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  obtain ⟨b,hb,hj,hg,cov⟩ := low_conductors k hl hh
  apply small_field_marked_orders (fun s => s=b) W k hl ⟨b,rfl,hb,hj,hg⟩ count
  exact roundedShortening_of_physical _ W k (by omega) cov step
#print axioms degree_eleven_through_twenty
end WaringFieldSmall
