import Waring.EndgameCompletionProductErrors
import Waring.EndgameCompletionMinorSeparation

/-! # Exact short rational arcs on one period -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.EndgameCompletion
open RestrictedSmoothArcs

def periodicShortArc (r δ : ℝ) : Set ℝ :=
  Set.Ioc 0 1 ∩ {x | ∃ m : ℤ,|x-(r+(m : ℝ))|≤δ}

theorem periodicShortArc_measurable (r δ : ℝ) : MeasurableSet (periodicShortArc r δ) := by
  unfold periodicShortArc
  apply measurableSet_Ioc.inter
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion (fun m : ℤ=>
    (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet)

theorem periodicShortArc_subset (r δ : ℝ) : periodicShortArc r δ⊆Set.Ioc 0 1 :=
  Set.inter_subset_left

theorem periodicShortArc_eq_inner {r δ : ℝ} (hl : δ<r) (hu : δ<1-r) :
    periodicShortArc r δ=Set.Icc (r-δ) (r+δ) := by
  ext x
  constructor
  · rintro ⟨hx,m,hm⟩
    have hb := abs_le.mp hm
    have hmR : (-1 : ℝ)<m ∧ (m : ℝ)<1 := by constructor <;> linarith [hx.1,hx.2]
    have hmZ : (-1 : ℤ)<m ∧ m<1 := by exact_mod_cast hmR
    have hm0 : m=0 := by omega
    subst m
    norm_num only [Int.cast_zero,add_zero] at hb
    exact ⟨by linarith,by linarith⟩
  · intro hx
    refine ⟨⟨by linarith [hx.1],by linarith [hx.2]⟩,0,?_⟩
    simp only [Int.cast_zero,add_zero,abs_le]
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem periodicShortArc_eq_zero {δ : ℝ} (hδ : 0≤δ) (hδhalf : δ<1/2) :
    periodicShortArc 0 δ=Set.Ioc 0 δ ∪ Set.Icc (1-δ) 1 := by
  ext x
  constructor
  · rintro ⟨hx,m,hm⟩
    simp only [zero_add] at hm
    have hb := abs_le.mp hm
    have hmR : (-1 : ℝ)<m ∧ (m : ℝ)<2 := by constructor <;> linarith [hx.1,hx.2]
    have hmZ : (-1 : ℤ)<m ∧ m<2 := by exact_mod_cast hmR
    have hm01 : m=0 ∨ m=1 := by omega
    rcases hm01 with rfl|rfl
    · left
      norm_num only [Int.cast_zero,sub_zero] at hb
      exact ⟨hx.1,hb.2⟩
    · right
      norm_num only [Int.cast_one] at hb
      exact ⟨by linarith,hx.2⟩
  · rintro (hx|hx)
    · refine ⟨⟨hx.1,by linarith [hx.2]⟩,0,?_⟩
      simp only [Int.cast_zero,add_zero,sub_zero,abs_le]
      exact ⟨by linarith [hx.1],hx.2⟩
    · refine ⟨⟨by linarith [hx.1],hx.2⟩,1,?_⟩
      simp only [Int.cast_one,zero_add,abs_le]
      exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem periodicShortArc_zero_integral {δ : ℝ} (hδ : 0≤δ) (hδhalf : δ<1/2)
    {F : ℝ→ℂ} (hF : Continuous F) (hper : Function.Periodic F 1) :
    (∫ x in periodicShortArc 0 δ,F x)=∫ β in -δ..δ,F β := by
  have hdis : Disjoint (Set.Ioc 0 δ) (Set.Icc (1-δ) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.2,hy.1]
  rw [periodicShortArc_eq_zero hδ hδhalf,
    setIntegral_union hdis measurableSet_Icc hF.integrableOn_Ioc hF.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hδ,
    ← intervalIntegral.integral_of_le (by linarith : 1-δ≤(1 : ℝ))]
  have hshift := intervalIntegral.integral_comp_add_right (f := F) (a := -δ) (b := 0) 1
  rw [show (fun x=>F (x+1))=F from funext hper] at hshift
  have hshift' : (∫ x in (1-δ)..1,F x)=∫ x in -δ..0,F x := by
    simpa only [zero_add,show -δ+1=1-δ by ring] using hshift.symm
  rw [hshift',add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
    (hF.intervalIntegrable _ _)

theorem arcLabelRat_lt_one (p : ArcLabel) : (arcLabelRat p : ℝ)<1 := by
  rw [arcLabelRat_real,div_lt_one (by exact_mod_cast p.1.pos : (0 : ℝ)<p.1)]
  exact_mod_cast ZMod.val_lt (p.2 : ZMod (p.1 : ℕ))

theorem arcLabelRat_margin (p : ArcLabel) (hp : (arcLabelRat p : ℝ)≠0) :
    1/(p.1 : ℝ)≤arcLabelRat p ∧ (arcLabelRat p : ℝ)≤1-1/(p.1 : ℝ) := by
  have hq : (0 : ℝ)<p.1 := by exact_mod_cast p.1.pos
  have ha : 1≤(p.2 : ZMod (p.1 : ℕ)).val := by
    by_contra hn
    have hz : (p.2 : ZMod (p.1 : ℕ)).val=0 := by omega
    apply hp
    simp only [arcLabelRat_real,hz,Nat.cast_zero,zero_div]
  have hb : ((p.2 : ZMod (p.1 : ℕ)).val : ℝ)+1≤(p.1 : ℝ) := by
    exact_mod_cast ZMod.val_lt (p.2 : ZMod (p.1 : ℕ))
  rw [arcLabelRat_real]
  refine ⟨div_le_div_of_nonneg_right (by exact_mod_cast ha) hq.le,?_⟩
  rw [le_sub_iff_add_le,← add_div,div_le_one hq]
  exact hb

theorem periodicShortArc_label_integral (p : ArcLabel) {δ : ℝ}
    (hδ : 0≤δ) (hδhalf : δ<1/2) (hδq : δ<1/(p.1 : ℝ))
    {F : ℝ→ℂ} (hF : Continuous F) (hper : Function.Periodic F 1) :
    (∫ x in periodicShortArc (arcLabelRat p) δ,F x)=
      ∫ β in -δ..δ,F ((arcLabelRat p : ℝ)+β) := by
  by_cases hr : (arcLabelRat p : ℝ)=0
  · simp only [hr,zero_add]
    exact periodicShortArc_zero_integral hδ hδhalf hF hper
  · have hm := arcLabelRat_margin p hr
    rw [periodicShortArc_eq_inner (hδq.trans_le hm.1) (by linarith [hm.2]),
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith :
        (arcLabelRat p : ℝ)-δ≤(arcLabelRat p : ℝ)+δ),
      intervalIntegral.integral_comp_add_left]
    congr 1 <;> ring

theorem periodicShortArc_label_disjoint {Q δ : ℝ} (hQ : 0≤Q) (hδ : 0≤δ)
    (hsmall : 4*Q^2*δ≤1) {p q : ArcLabel}
    (hp : (p.1 : ℝ)≤Q) (hq : (q.1 : ℝ)≤Q) (hne : p≠q) :
    Disjoint (periodicShortArc (arcLabelRat p) δ) (periodicShortArc (arcLabelRat q) δ) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hx,m,hm⟩ ⟨_,n,hn⟩
  let r : ℚ := arcLabelRat p+m
  let s : ℚ := arcLabelRat q+n
  have hr : (r.den : ℝ)≤Q := by simpa only [r,Rat.add_intCast_den,arcLabelRat_den] using hp
  have hs : (s.den : ℝ)≤Q := by simpa only [s,Rat.add_intCast_den,arcLabelRat_den] using hq
  have hband (t : ℚ) (ht : (t.den : ℝ)≤Q) (hh : |x-(t : ℝ)|≤δ) :
      x∈rationalBand t (Q*δ) := by
    change |(t.den : ℝ)*x-(t.num : ℝ)|≤Q*δ
    rw [RationalHeight.denominator_error]
    exact mul_le_mul ht hh (abs_nonneg _) hQ
  have he := rationalBand_unique (mul_nonneg hQ hδ)
    (by nlinarith : 4*Q*(Q*δ)≤1) hr hs
    (hband r hr (by simpa only [r,Rat.cast_add,Rat.cast_intCast] using hm))
    (hband s hs (by simpa only [s,Rat.cast_add,Rat.cast_intCast] using hn))
  have heR : (arcLabelRat p : ℝ)+(m : ℝ)=(arcLabelRat q : ℝ)+(n : ℝ) := by
    exact_mod_cast he
  have hmnr : (-1 : ℝ)<((m-n : ℤ) : ℝ) ∧ ((m-n : ℤ) : ℝ)<1 := by
    push_cast
    constructor <;> linarith [(arcLabelRat_bounds p).1,(arcLabelRat_bounds q).1,
      arcLabelRat_lt_one p,arcLabelRat_lt_one q]
  have hmnz : (-1 : ℤ)<m-n ∧ m-n<1 := by exact_mod_cast hmnr
  have hmn : m=n := by omega
  rw [hmn] at heR
  apply hne
  apply arcLabelRat_injective
  exact_mod_cast add_right_cancel heR

#print axioms periodicShortArc_label_integral
#print axioms periodicShortArc_label_disjoint
end Waring.EndgameCompletion
