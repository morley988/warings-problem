import Waring.RestrictedSmoothMean
import Waring.HeightMeasurability

/-! # Literal rational-height sublevels lie in the proved major regions -/

noncomputable section
open MeasureTheory
namespace Waring.RestrictedSmoothArcs
open SmoothMoments EndgameCompletion

theorem arcLabelRat_one : arcLabelRat ⟨1,(1 : (ZMod 1)ˣ)⟩=0 := by
  apply Rat.ext <;> norm_num [arcLabelRat]

theorem mem_periodicMajorRegion_zero {Q δ x : ℝ} (hQ : 1 ≤ Q)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) (hnear : |x| ≤ δ ∨ |x-1| ≤ δ) :
    x ∈ periodicMajorRegion (broadDenominators Q) δ := by
  rw [mem_periodicMajorRegion]
  refine ⟨hx,1,(mem_broadDenominators Q 1).mpr (by simpa using hQ),1,?_⟩
  rw [arcLabelRat_one,wrappedRationalBand]
  rcases hnear with hnear | hnear
  · exact Or.inl (by simpa [rationalBand] using hnear)
  · right
    have hh := abs_le.mp hnear
    simp only [Rat.cast_zero,Rat.den_zero,Nat.cast_one,div_one,zero_sub,zero_add,Set.mem_Icc]
    constructor <;> linarith

theorem rationalBand_subset_periodicMajorRegion {Q δ x : ℝ} (hQ : 1 ≤ Q)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) {r : ℚ} (hq : (r.den : ℝ) ≤ Q)
    (hr : x ∈ rationalBand r δ) :
    x ∈ periodicMajorRegion (broadDenominators Q) δ := by
  by_cases hδ : 1 ≤ δ
  · exact mem_periodicMajorRegion_zero hQ hx (Or.inl (by
      rw [abs_of_pos hx.1]
      exact hx.2.trans hδ))
  have hδlt : δ < 1 := lt_of_not_ge hδ
  have hd : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hdp : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  change |(r.den : ℝ)*x-(r.num : ℝ)| ≤ δ at hr
  have he := abs_le.mp hr
  have hnum0 : (0 : ℤ) ≤ r.num := by
    have hreal : (-1 : ℝ) < r.num := by nlinarith [mul_pos hdp hx.1]
    have hint : (-1 : ℤ) < r.num := by exact_mod_cast hreal
    omega
  have hnumq : r.num ≤ (r.den : ℤ) := by
    have hreal : (r.num : ℝ) < (r.den : ℝ)+1 := by
      nlinarith [mul_le_mul_of_nonneg_left hx.2 hdp.le]
    have hint : r.num < (r.den : ℤ)+1 := by exact_mod_cast hreal
    omega
  by_cases hlast : r.num=(r.den : ℤ)
  · apply mem_periodicMajorRegion_zero hQ hx
    right
    have ha : (r.num : ℝ)=(r.den : ℝ) := by exact_mod_cast hlast
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    rw [ha] at he
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hx.2)]
  have hnumlt : r.num < (r.den : ℤ) := lt_of_le_of_ne hnumq hlast
  have hna : (r.num.natAbs : ℤ)=r.num := by
    rw [Int.natCast_natAbs,abs_of_nonneg hnum0]
  have hnalt : r.num.natAbs < r.den := by exact_mod_cast (hna ▸ hnumlt)
  let q : ℕ+ := ⟨r.den,r.pos⟩
  let a : (ZMod (q : ℕ))ˣ := ZMod.unitOfCoprime r.num.natAbs r.reduced
  have hrat : arcLabelRat ⟨q,a⟩=r := by
    apply Rat.ext
    · change ((a : ZMod (q : ℕ)).val : ℤ)=r.num
      simp only [a,ZMod.coe_unitOfCoprime,ZMod.val_natCast,show (q : ℕ)=r.den from rfl,
        Nat.mod_eq_of_lt hnalt]
      exact hna
    · rfl
  rw [mem_periodicMajorRegion]
  refine ⟨hx,q,(mem_broadDenominators Q q).mpr hq,a,?_⟩
  rw [hrat]
  exact Or.inl hr

theorem height_sublevel_subset_periodicMajorRegion {V Q : ℝ} (hV : 0 < V) (hQ : 1 ≤ Q) :
    Set.Ioc (0 : ℝ) 1 ∩ {x | RationalHeight.height V x ≤ Q} ⊆
      periodicMajorRegion (broadDenominators Q) (Q/V) := by
  rintro x ⟨hx,hheight⟩
  obtain ⟨r,hr⟩ := RationalHeight.exists_minimizer hV x
  have hc : RationalHeight.cost V x r ≤ Q := hr ▸ hheight
  have hq : (r.den : ℝ) ≤ Q := (le_max_left _ _).trans hc
  apply rationalBand_subset_periodicMajorRegion hQ hx hq
  change |(r.den : ℝ)*x-(r.num : ℝ)| ≤ Q/V
  apply (le_div_iff₀ hV).mpr
  simpa only [mul_comm] using (le_max_right _ _).trans hc

#print axioms height_sublevel_subset_periodicMajorRegion
end Waring.RestrictedSmoothArcs
