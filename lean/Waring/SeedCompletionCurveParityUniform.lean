import Waring.SeedCompletionCurveUniform
import Waring.SeedCompletionCurveParity

/-! # Uniform two-thirds curve counting for either common parity -/

noncomputable section
open scoped BigOperators Polynomial Polynomial.Bivariate
open Polynomial
namespace Waring.SeedCompletionCurveParityUniform
open SeedCompletionCurveElimination SeedCompletionCurveFactors
open SeedCompletionCurveTranslation SeedCompletionCurveLattice SeedCompletionCurveUniform

/-- Every positive translated self-intersection of an actual component has
bounded cardinality, uniformly in all coefficients and translation sizes. -/
theorem component_translation_card_le_parity {f g : ℝ[X]} {σ : ℝ}
    (hf : 0 < f.natDegree) (hdegree : f.natDegree=g.natDegree)
    (hleading : f.leadingCoeff=g.leadingCoeff)
    (hσ : σ^2=1) (hparf : ∀ t : ℝ,f.eval (-t)=σ*f.eval t) (hparg : ∀ t : ℝ,g.eval (-t)=σ*g.eval t)
    (hne : f ≠ g) {p : ℝ[X][Y]} (hp : p ∈ curveFactors (separatedCurve f g))
    (S : Finset (ℕ×ℕ))
    (hpoints : ∀ z ∈ S,p.evalEval (z.1 : ℝ) (z.2 : ℝ)=0)
    (hinj : Set.InjOn Prod.fst (↑S : Set (ℕ×ℕ)))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (S.filter (fun z => (z.1+a,z.2+b) ∈ S)).card ≤ 2*f.natDegree^2 := by
  classical
  let A := S.filter (fun z => (z.1+a,z.2+b) ∈ S)
  by_cases hA : A.Nonempty
  · obtain ⟨z,hz⟩ := hA
    have hg : 0 < g.natDegree := by omega
    have hunit := separatedCurve_leadingCoeff_isUnit f hg
    have hF : separatedCurve f g ≠ 0 := leadingCoeff_ne_zero.mp hunit.ne_zero
    have hmon := curveFactor_monic hunit hp
    have hdiv := curveFactor_dvd hp
    have hpos := curveFactor_natDegree_pos hunit hp
    have hnot : translate p (a : ℝ) (b : ℝ) ≠ p :=
      translate_ne_of_divides_separated_parity hf hdegree hleading
        (by exact_mod_cast ha) (by exact_mod_cast hb) hσ hparf hparg hne hdiv
        (hpoints z (Finset.mem_filter.mp hz).1)
    have hnotdiv : ¬p ∣ translate p (a : ℝ) (b : ℝ) := by
      intro h
      exact hnot (eq_of_monic_of_dvd_of_natDegree_le hmon
        (translate_monic hmon _ _) h (by rw [translate_natDegree]))
    have hDX : (Bivariate.swap (separatedCurve f g)).natDegree=f.natDegree :=
      separatedCurve_swap_natDegree g hf
    have hbound := natural_common_points_card_le p (translate p (a : ℝ) (b : ℝ))
      p.natDegree f.natDegree hpos (curveFactor_prime hp) rfl (translate_natDegree p _ _)
      hnotdiv (fun n => (factor_coefficient_natDegree_le hF hdiv n).trans_eq hDX)
      (fun n => (translate_factor_coefficient_natDegree_le hF hdiv _ _ n).trans_eq hDX)
      A (by
        intro w hw
        have hwS := (Finset.mem_filter.mp hw).1
        have hwshift := (Finset.mem_filter.mp hw).2
        refine ⟨hpoints w hwS,?_⟩
        rw [evalEval_translate]
        simpa only [Nat.cast_add] using hpoints (w.1+a,w.2+b) hwshift)
      (hinj.mono (Finset.filter_subset _ _))
    have hpD : p.natDegree ≤ f.natDegree := by
      have hh := natDegree_le_of_dvd hdiv hF
      rwa [separatedCurve_natDegree f hg,← hdegree] at hh
    exact hbound.trans (by nlinarith)
  · have hz : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ _
    rw [hz,Finset.card_empty]
    exact Nat.zero_le _

/-- The actual finite curve count. The explicit constant depends only on
the common degree; no coefficient-size or coefficient-separation premise
is required. -/
theorem separated_parity_curve_card_bound {f g : ℝ[X]} {σ : ℝ}
    (hf : 0 < f.natDegree) (hdegree : f.natDegree=g.natDegree)
    (hleading : f.leadingCoeff=g.leadingCoeff)
    (hσ : σ^2=1) (hparf : ∀ t : ℝ,f.eval (-t)=σ*f.eval t) (hparg : ∀ t : ℝ,g.eval (-t)=σ*g.eval t)
    (hne : f ≠ g) (S : Finset (ℕ×ℕ)) (P : ℝ) (hP : 1 ≤ P)
    (hbox : ∀ z ∈ S,(z.1 : ℝ) ≤ P ∧ (z.2 : ℝ) ≤ P)
    (hpoints : ∀ z ∈ S,f.eval (z.1 : ℝ)=g.eval (z.2 : ℝ))
    (hinj : Set.InjOn Prod.fst (↑S : Set (ℕ×ℕ)))
    (horder : ∀ z ∈ S,∀ w ∈ S,z.1 < w.1 → z.2 < w.2) :
    (S.card : ℝ) ≤ (f.natDegree : ℝ)*(8*(f.natDegree : ℝ)^2+3)*P^(2/3 : ℝ) := by
  classical
  let F := separatedCurve f g
  let factors := curveFactors F
  let component := fun p : ℝ[X][Y] => S.filter (fun z => p.evalEval (z.1 : ℝ) (z.2 : ℝ)=0)
  let B := 2*f.natDegree^2
  have hg : 0 < g.natDegree := by omega
  have hunit : IsUnit F.leadingCoeff := separatedCurve_leadingCoeff_isUnit f hg
  have hfactorCount : factors.card ≤ f.natDegree := by
    have h := curveFactors_card_le hunit
    rwa [separatedCurve_natDegree f hg,← hdegree] at h
  have hcomponent (p : ℝ[X][Y]) (hp : p ∈ factors) :
      ((component p).card : ℝ) ≤ (4*(B : ℝ)+3)*P^(2/3 : ℝ) := by
    apply monotone_set_card_bound (component p) P hP
      (fun z hz => hbox z (Finset.mem_filter.mp hz).1)
      (hinj.mono (Finset.filter_subset _ _))
      (fun z hz w hw hzw => horder z (Finset.mem_filter.mp hz).1
        w (Finset.mem_filter.mp hw).1 hzw) B
    intro a b ha hb
    exact component_translation_card_le_parity hf hdegree hleading hσ hparf hparg hne hp
      (component p) (fun z hz => (Finset.mem_filter.mp hz).2)
      (hinj.mono (Finset.filter_subset _ _)) a b ha hb
  have hcover : S ⊆ factors.biUnion component := by
    intro z hz
    have hzero : F.evalEval (z.1 : ℝ) (z.2 : ℝ)=0 := by
      rw [evalEval_separatedCurve,hpoints z hz,sub_self]
    obtain ⟨p,hp,hpz⟩ := exists_curveFactor_zero hunit _ _ hzero
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hz,hpz⟩⟩
  have hcount : S.card ≤ ∑ p ∈ factors,(component p).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hnonneg : 0 ≤ (4*(B : ℝ)+3)*P^(2/3 : ℝ) := by positivity
  calc
    (S.card : ℝ) ≤ ∑ p ∈ factors,((component p).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _p ∈ factors,((4*(B : ℝ)+3)*P^(2/3 : ℝ)) :=
      Finset.sum_le_sum hcomponent
    _ = (factors.card : ℝ)*((4*(B : ℝ)+3)*P^(2/3 : ℝ)) := by simp
    _ ≤ (f.natDegree : ℝ)*((4*(B : ℝ)+3)*P^(2/3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hfactorCount) hnonneg
    _ = _ := by dsimp [B]; push_cast; ring

#print axioms component_translation_card_le_parity
#print axioms separated_parity_curve_card_bound
end Waring.SeedCompletionCurveParityUniform
