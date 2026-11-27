import Waring.EndgameCompletionNarrowBands

/-! # Exact finite decomposition of the periodic narrow core -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.EndgameCompletion
open RestrictedSmoothArcs

def narrowDenominators (N : ℕ) : Finset ℕ+ := broadDenominators ((N-1 : ℕ) : ℝ)

theorem mem_narrowDenominators (N : ℕ) (q : ℕ+) :
    q∈narrowDenominators N↔(q : ℕ)<N := by
  rw [narrowDenominators,mem_broadDenominators]
  have hq := q.pos
  norm_cast
  omega

theorem rectangleCoreGlobal_period_eq (k N : ℕ) (P : ℝ) :
    Set.Ioc 0 1 ∩ rectangleCoreGlobal k P N=
      ⋃ p∈denominatorArcLabels (narrowDenominators N),
        periodicShortArc (arcLabelRat p) ((N : ℝ)/P^k) := by
  ext x
  constructor
  · rintro ⟨hx,q,hq,a,m,hm⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨⟨q,a⟩,?_,hx,m,?_⟩
    · simp only [denominatorArcLabels,Finset.mem_sigma,Finset.mem_univ,and_true,
        mem_narrowDenominators]
      exact hq
    · simpa only [arcLabelRat_real] using hm
  · intro hx
    obtain ⟨⟨q,a⟩,hp,hx,m,hm⟩ := Set.mem_iUnion₂.mp hx
    have hq : (q : ℕ)<N := by
      simpa only [denominatorArcLabels,Finset.mem_sigma,Finset.mem_univ,and_true,
        mem_narrowDenominators] using hp
    exact ⟨hx,q,hq,a,m,by simpa only [arcLabelRat_real] using hm⟩

theorem narrow_width_bounds {N : ℕ} (hN : 1≤N) {δ : ℝ} (hδ : 0≤δ)
    (hsmall : 4*(N : ℝ)^2*δ≤1) :
    δ<1/2 ∧ ∀ q : ℕ+,(q : ℕ)<N→δ<1/(q : ℝ) := by
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hN2 : (1 : ℝ)≤(N : ℝ)^2 := by nlinarith
  have hδ4 : 4*δ≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN2) hδ]
  refine ⟨by linarith,?_⟩
  intro q hq
  have hqR : (q : ℝ)≤(N : ℝ)^2 := by
    have hqN : (q : ℝ)<N := by exact_mod_cast hq
    nlinarith
  apply (lt_div_iff₀ (by exact_mod_cast q.pos : (0 : ℝ)<q)).mpr
  have hh := mul_le_mul_of_nonneg_left hqR hδ
  nlinarith

theorem narrow_radius_packing {P : ℝ} (hP : 0<P) (k N : ℕ)
    (hsmall : 4*(N : ℝ)^3≤P^k) :
    4*(N : ℝ)^2*((N : ℝ)/P^k)≤1 := by
  rw [← mul_div_assoc]
  apply (div_le_one (pow_pos hP k)).mpr
  convert hsmall using 1 <;> ring

theorem rectangleCoreGlobal_period_integral_eq (k N : ℕ) {P : ℝ}
    (hP : 0<P) (hN : 1≤N) (hsmall : 4*(N : ℝ)^3≤P^k)
    {F : ℝ→ℂ} (hF : Continuous F) (hper : Function.Periodic F 1) :
    (∫ x in Set.Ioc 0 1 ∩ rectangleCoreGlobal k P N,F x)=
      ∑ q∈narrowDenominators N,∑ a : (ZMod (q : ℕ))ˣ,
        ∫ β in -((N : ℝ)/P^k)..((N : ℝ)/P^k),
          F (((a : ZMod (q : ℕ)).val : ℝ)/(q : ℝ)+β) := by
  classical
  let δ : ℝ := (N : ℝ)/P^k
  let A := denominatorArcLabels (narrowDenominators N)
  have hδ : 0≤δ := div_nonneg (Nat.cast_nonneg _) (pow_pos hP k).le
  have hpack : 4*(N : ℝ)^2*δ≤1 := narrow_radius_packing hP k N hsmall
  have hw := narrow_width_bounds hN hδ hpack
  have hq (p : ArcLabel) (hp : p∈A) : (p.1 : ℕ)<N := by
    simpa only [A,denominatorArcLabels,Finset.mem_sigma,Finset.mem_univ,and_true,
      mem_narrowDenominators] using hp
  have hpair : Set.Pairwise (↑A : Set ArcLabel)
      (fun p q=>Disjoint (periodicShortArc (arcLabelRat p) δ) (periodicShortArc (arcLabelRat q) δ)) := by
    intro p hp q hq' hne
    exact periodicShortArc_label_disjoint (Nat.cast_nonneg N) hδ hpack
      (by exact_mod_cast (hq p hp).le) (by exact_mod_cast (hq q hq').le) hne
  rw [rectangleCoreGlobal_period_eq]
  change (∫ x in ⋃ p∈A,periodicShortArc (arcLabelRat p) δ,F x)=_
  rw [integral_biUnion_finset A (fun p _=>periodicShortArc_measurable _ _) hpair
    (fun p _=>hF.integrableOn_Ioc.mono_set (periodicShortArc_subset _ _))]
  calc
    _ = ∑ p∈A,∫ β in -δ..δ,F ((arcLabelRat p : ℝ)+β) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact periodicShortArc_label_integral p hδ hw.1 (hw.2 p.1 (hq p hp)) hF hper
    _ = _ := by simp only [A,denominatorArcLabels,Finset.sum_sigma,arcLabelRat_real,δ]

#print axioms rectangleCoreGlobal_period_integral_eq
end Waring.EndgameCompletion
