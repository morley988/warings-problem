import Waring.EndgameCompletionNarrowCore

/-! # Exact ordinary narrow-core arc decomposition -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.EndgameCompletion
open RestrictedSmoothArcs

theorem narrow_denominator_le_P {k N : ℕ} (hk : 1≤k) (hN : 1≤N) {P : ℝ}
    (hsize : 2*(k : ℝ)*(N : ℝ)^2≤P) (q : ℕ+) (hq : (q : ℕ)<N) : (q : ℝ)≤P := by
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hqR : (q : ℝ)<N := by exact_mod_cast hq
  have hh := mul_nonneg (sub_nonneg.mpr hkR) (sq_nonneg (N : ℝ))
  nlinarith

theorem narrow_radius_le_broad {k N : ℕ} (hk : 1≤k) {P : ℝ} (hP : 0<P)
    (hsize : 2*(k : ℝ)*(N : ℝ)^2≤P) (q : ℕ+) (hq : (q : ℕ)<N) :
    (N : ℝ)/P^k≤broadArcWidth k P/(q : ℝ) := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hqR : (0 : ℝ)<q := by exact_mod_cast q.pos
  have hqN : (q : ℝ)≤N := by exact_mod_cast hq.le
  have hNq : 2*(k : ℝ)*(N : ℝ)*(q : ℝ)≤P := by
    have hh := mul_nonneg (by positivity : (0 : ℝ)≤2*(k : ℝ)*(N : ℝ))
      (sub_nonneg.mpr hqN)
    nlinarith
  unfold broadArcWidth
  rw [inv_eq_one_div,div_div]
  apply (div_le_div_iff₀ (pow_pos hP k) (by positivity :
    (0 : ℝ)<(2*(k : ℝ)*P^(k-1))*(q : ℝ))).mpr
  have hp : P^k=P^(k-1)*P := by rw [← pow_succ,Nat.sub_add_cancel hk]
  rw [hp,one_mul]
  have hh := mul_le_mul_of_nonneg_right hNq (pow_pos hP (k-1)).le
  nlinarith

theorem periodicShortArc_subset_wrapped (p : ArcLabel) {δ w : ℝ}
    (hδ : 0≤δ) (hδhalf : δ<1/2) (hδq : δ<1/(p.1 : ℝ))
    (hw : δ≤w/(p.1 : ℝ)) :
    periodicShortArc (arcLabelRat p) δ⊆wrappedRationalBand (arcLabelRat p) w := by
  intro x hx
  by_cases hr : (arcLabelRat p : ℝ)=0
  · rw [hr,periodicShortArc_eq_zero hδ hδhalf] at hx
    rcases hx with hx|hx
    · left
      rw [rationalBand_eq_Icc,hr,arcLabelRat_den]
      exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
    · right
      change (arcLabelRat p : ℝ)-w/(arcLabelRat p).den+1≤x ∧
        x≤(arcLabelRat p : ℝ)+w/(arcLabelRat p).den+1
      rw [hr,arcLabelRat_den]
      exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · have hm := arcLabelRat_margin p hr
    rw [periodicShortArc_eq_inner (hδq.trans_le hm.1) (by linarith [hm.2])] at hx
    left
    rw [rationalBand_eq_Icc,arcLabelRat_den]
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem rectangleCoreGlobal_period_subset_broad {k N : ℕ} (hk : 1≤k) (hN : 1≤N)
    {P : ℝ} (hP : 0<P) (hsize : 2*(k : ℝ)*(N : ℝ)^2≤P)
    (hpack : 4*(N : ℝ)^3≤P^k) :
    Set.Ioc 0 1 ∩ rectangleCoreGlobal k P N⊆ordinaryBroadMajor k P := by
  intro x hx
  rw [rectangleCoreGlobal_period_eq] at hx
  obtain ⟨p,hp,hx⟩ := Set.mem_iUnion₂.mp hx
  have hq : (p.1 : ℕ)<N := by
    simpa only [denominatorArcLabels,Finset.mem_sigma,Finset.mem_univ,and_true,
      mem_narrowDenominators] using hp
  have hδ : 0≤(N : ℝ)/P^k := by positivity
  have hw := narrow_width_bounds hN hδ (narrow_radius_packing hP k N hpack)
  apply (mem_periodicMajorRegion _ _ _).mpr
  refine ⟨hx.1,p.1,?_,p.2,?_⟩
  · exact (mem_broadDenominators P p.1).mpr (narrow_denominator_le_P hk hN hsize p.1 hq)
  · exact periodicShortArc_subset_wrapped p hδ hw.1 (hw.2 p.1 hq)
      (narrow_radius_le_broad hk hP hsize p.1 hq) hx

theorem ordinaryCore_eq_narrow_period {k N : ℕ} (hk : 1≤k) (hN : 1≤N)
    {P : ℝ} (hP : 0<P) (hsize : 2*(k : ℝ)*(N : ℝ)^2≤P)
    (hpack : 4*(N : ℝ)^3≤P^k) :
    ordinaryCore k P N=Set.Ioc 0 1 ∩ rectangleCoreGlobal k P N := by
  ext x
  constructor
  · intro hx
    exact ⟨ordinaryBroadMajor_subset k P hx.1,hx.2⟩
  · intro hx
    exact ⟨rectangleCoreGlobal_period_subset_broad hk hN hP hsize hpack hx,hx.2⟩

/-- Exact complex arc decomposition, with the strict denominator cutoff
and zero/one wrap matching the actual pruning core. -/
theorem ordinaryCore_integral_eq_arc_sum {k N : ℕ} (hk : 1≤k) (hN : 1≤N)
    {P : ℝ} (hP : 0<P) (hsize : 2*(k : ℝ)*(N : ℝ)^2≤P)
    (hpack : 4*(N : ℝ)^3≤P^k)
    {F : ℝ→ℂ} (hF : Continuous F) (hper : Function.Periodic F 1) :
    (∫ x in ordinaryCore k P N,F x)=
      ∑ q∈broadDenominators ((N-1 : ℕ) : ℝ),∑ a : (ZMod (q : ℕ))ˣ,
        ∫ β in -((N : ℝ)/P^k)..((N : ℝ)/P^k),
          F (((a : ZMod (q : ℕ)).val : ℝ)/(q : ℝ)+β) := by
  rw [ordinaryCore_eq_narrow_period hk hN hP hsize hpack]
  exact rectangleCoreGlobal_period_integral_eq k N hP hN hpack hF hper

#print axioms ordinaryCore_integral_eq_arc_sum
end Waring.EndgameCompletion
