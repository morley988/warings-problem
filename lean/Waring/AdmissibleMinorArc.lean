import Waring.MixedEndgame
import Waring.ConditionalMoments

/-!
# From actual admissible moments to the composed conditional Waring bounds

Full-interval real moments dominate restricted ENNReal arc moments. The two
needed smooth bounds share one positive smoothness exponent and one finite
constant. Thus the published seed tables plus the explicit analytic policy
soundness premises feed the actual mixed-integral endgame. Ordinary minor
moments, positive core estimates and pruning remain named analytic hypotheses.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped ENNReal Topology

namespace Waring.AdmissibleMinorArc
open Waring.SmoothMoments Waring.MixedEndgame Waring.Certificate Waring.Endgame

def epsilon8 : ℝ := 7/400000
def epsilon9 : ℝ := 1/8000

theorem epsilon8_pos : 0 < epsilon8 := by norm_num [epsilon8]
theorem epsilon9_pos : 0 < epsilon9 := by norm_num [epsilon9]
theorem epsilon8_budget : epsilon8 ≤ 7/200000 := by norm_num [epsilon8]
theorem epsilon9_budget : epsilon9 ≤ 1/4000 := by norm_num [epsilon9]

/-- The full ENNReal arc moment is the embedding of the actual real moment. -/
theorem smoothArcMoment_full (k p : ℕ) (P R : ℝ) :
    smoothArcMoment k p P R (Set.Ioc 0 1) = ENNReal.ofReal (smoothMoment k p P R) := by
  unfold smoothArcMoment absoluteSmooth smoothMoment
  rw [intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal (smoothMoment_integrable k p P R).1
      (Filter.Eventually.of_forall (fun α => pow_nonneg (norm_nonneg _) p))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

/-- Restricting the integration domain only decreases the nonnegative moment. -/
theorem smoothArcMoment_le_full (k p : ℕ) (P R : ℝ) {A : Set ℝ}
    (hA : A ⊆ Set.Ioc 0 1) :
    smoothArcMoment k p P R A ≤ ENNReal.ofReal (smoothMoment k p P R) := by
  rw [← smoothArcMoment_full]
  exact lintegral_mono_set hA

/-- Transfer a finite real moment bound to any minor-arc subset. -/
theorem smoothArcMoment_le_of_bound (k p : ℕ) {P R C exponent : ℝ} {A : Set ℝ}
    (hP : 0 < P) (hC : 0 ≤ C) (hA : A ⊆ Set.Ioc 0 1)
    (h : smoothMoment k p P R ≤ C*P^exponent) :
    smoothArcMoment k p P R A ≤ ENNReal.ofReal C * ENNReal.ofReal P ^ exponent := by
  rw [ENNReal.ofReal_rpow_of_pos hP, ← ENNReal.ofReal_mul hC]
  exact (smoothArcMoment_le_full k p P R hA).trans (ENNReal.ofReal_le_ofReal h)

theorem minor_subset_period {core pruning minor : Set ℝ}
    (h : ArcPartition core pruning minor) : minor ⊆ Set.Ioc 0 1 := by
  rw [← h.cover]
  exact Set.subset_union_right.trans Set.subset_union_right

/-- Admissible degree-eight excesses provide a common eta that can be used in
any actual endgame satisfying the remaining displayed analytic hypotheses. -/
theorem waring8_of_admissible_excesses
    (h32 : AdmissibleExcess 8 32 delta8_32) (h34 : AdmissibleExcess 8 34 delta8_34) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n ^ η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*P n^(30 : ℝ) ≤ arcContribution 8 8 30 (P n) (R n) n (core n)) →
        ((fun n => arcContribution 8 8 30 (P n) (R n) n (pruning n)) =o[atTop]
          (fun n => P n^(30 : ℝ))) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 72 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(63+epsilon8)) →
        WaringBound 8 38 := by
  have h32' : AdmissibleExponent 8 32 (24+delta8_32) := by
    unfold AdmissibleExcess at h32
    norm_num only [Nat.cast_ofNat] at h32
    exact h32
  have h34' : AdmissibleExponent 8 34 (26+delta8_34) := by
    unfold AdmissibleExcess at h34
    norm_num only [Nat.cast_ofNat] at h34
    exact h34
  rcases admissibleExponent_pair h32' h34' epsilon8_pos with
    ⟨η,hη,C,hC,P₀,hP₀,hbounds⟩
  refine ⟨η,hη,?_⟩
  intro P R core pruning minor hP hR hpartition c hc hcore hpruning C₀ hC₀ hord
  apply MixedEndgame.waring8_conditional P R core pruning minor hP hpartition hc hcore hpruning
    hC₀ (C₁ := ENNReal.ofReal C) (C₂ := ENNReal.ofReal C)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top epsilon8_budget
  filter_upwards [hP.eventually_ge_atTop P₀,hR,hpartition,hord] with n hPn hRn hpart horn
  have hPpos : 0 < P n := zero_lt_one.trans_le (hP₀.trans hPn)
  have hs := hbounds (P n) hPn (R n) hRn.1 hRn.2
  exact ⟨horn,smoothArcMoment_le_of_bound 8 32 hPpos hC.le (minor_subset_period hpart) hs.1,
    smoothArcMoment_le_of_bound 8 34 hPpos hC.le (minor_subset_period hpart) hs.2⟩

/-- Degree-nine counterpart with the same explicit smoothness and constant scope. -/
theorem waring9_of_admissible_excesses
    (h38 : AdmissibleExcess 9 38 delta9_38) (h40 : AdmissibleExcess 9 40 delta9_40) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n ^ η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*P n^(37 : ℝ) ≤ arcContribution 9 11 35 (P n) (R n) n (core n)) →
        ((fun n => arcContribution 9 11 35 (P n) (R n) n (pruning n)) =o[atTop]
          (fun n => P n^(37 : ℝ))) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 9 90 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(80+epsilon9)) →
        WaringBound 9 46 := by
  have h38' : AdmissibleExponent 9 38 (29+delta9_38) := by
    unfold AdmissibleExcess at h38
    norm_num only [Nat.cast_ofNat] at h38
    exact h38
  have h40' : AdmissibleExponent 9 40 (31+delta9_40) := by
    unfold AdmissibleExcess at h40
    norm_num only [Nat.cast_ofNat] at h40
    exact h40
  rcases admissibleExponent_pair h38' h40' epsilon9_pos with
    ⟨η,hη,C,hC,P₀,hP₀,hbounds⟩
  refine ⟨η,hη,?_⟩
  intro P R core pruning minor hP hR hpartition c hc hcore hpruning C₀ hC₀ hord
  apply MixedEndgame.waring9_conditional P R core pruning minor hP hpartition hc hcore hpruning
    hC₀ (C₁ := ENNReal.ofReal C) (C₂ := ENNReal.ofReal C)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top epsilon9_budget
  filter_upwards [hP.eventually_ge_atTop P₀,hR,hpartition,hord] with n hPn hRn hpart horn
  have hPpos : 0 < P n := zero_lt_one.trans_le (hP₀.trans hPn)
  have hs := hbounds (P n) hPn (R n) hRn.1 hRn.2
  exact ⟨horn,smoothArcMoment_le_of_bound 9 38 hPpos hC.le (minor_subset_period hpart) hs.1,
    smoothArcMoment_le_of_bound 9 40 hPpos hC.le (minor_subset_period hpart) hs.2⟩

/-- The entire checked degree-eight arithmetic, its semantic finite iteration,
and the actual representation endgame compose under precisely these remaining
source/policy and circle-method estimates. This is NOT an unconditional theorem. -/
theorem waring8_from_seed_tables_conditional
    (hseed : AdmissibleCurve 8 source8)
    (hcoefficientSeed : AdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n ^ η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*P n^(30 : ℝ) ≤ arcContribution 8 8 30 (P n) (R n) n (core n)) →
        ((fun n => arcContribution 8 8 30 (P n) (R n) n (pruning n)) =o[atTop]
          (fun n => P n^(30 : ℝ))) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 72 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(63+epsilon8)) →
        WaringBound 8 38 := by
  have h := final8_excesses_conditional hseed hcoefficientSeed hsound
  exact waring8_of_admissible_excesses h.1 h.2

theorem waring9_from_seed_tables_conditional
    (hseed : AdmissibleCurve 9 source9)
    (hcoefficientSeed : AdmissibleCurve 18 coefficientSource9)
    (hsound : ∀ i, i < policies9.size → AnalyticPolicySound 9 policies9[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n ^ η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*P n^(37 : ℝ) ≤ arcContribution 9 11 35 (P n) (R n) n (core n)) →
        ((fun n => arcContribution 9 11 35 (P n) (R n) n (pruning n)) =o[atTop]
          (fun n => P n^(37 : ℝ))) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 9 90 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(80+epsilon9)) →
        WaringBound 9 46 := by
  have h := final9_excesses_conditional hseed hcoefficientSeed hsound
  exact waring9_of_admissible_excesses h.1 h.2

#print axioms smoothArcMoment_full
#print axioms waring8_from_seed_tables_conditional
#print axioms waring9_from_seed_tables_conditional
end Waring.AdmissibleMinorArc
