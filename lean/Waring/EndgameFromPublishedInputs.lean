import Waring.Pruning

/-!
# The complete conditional Waring endgame with explicit source estimates

These theorems combine the kernel-checked finite certificates, actual
admissibility semantics, actual mixed coefficient counts, minor-arc Holder
bounds and the proved pruning estimates. The remaining number-theoretic source
estimates are explicit premises, including the strong degree-eight 42nd moment
without a P^epsilon loss. The file does not assert that those source results or
analytic policy soundness have already been formalized.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped ENNReal Topology

namespace Waring.EndgameFromPublishedInputs
open SmoothMoments MixedEndgame AdmissibleMinorArc Certificate Pruning

theorem pruning_subset_period {core pruning minor : Set ℝ}
    (h : ArcPartition core pruning minor) : pruning ⊆ Set.Ioc 0 1 := by
  rw [← h.cover]
  exact Set.subset_union_left.trans Set.subset_union_right

/-- A complete conditional path to the degree-eight Waring bound. Pruning
little-o is proved from the displayed ordinary pruning moment and strong full
smooth moment; it is no longer a separate analytic premise. -/
theorem waring8_from_source_estimates
    (hseed : AdmissibleCurve 8 source8)
    (hcoefficientSeed : AdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R W : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop → Tendsto W atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n^η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*(P n)^(30 : ℝ) ≤
          arcContribution 8 8 30 (P n) (R n) n (core n)) →
        ∀ Cf Cg : ℝ, 0 < Cf → 0 < Cg →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (pruning n) ≤
          ENNReal.ofReal (Cf*(P n)^4*(W n)^(-(1/16 : ℝ)))) →
        (∀ᶠ n in atTop, smoothMoment 8 42 (P n) (R n) ≤ Cg*(P n)^34) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 72 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(63+epsilon8)) →
        WaringBound 8 38 := by
  obtain ⟨η,hη,hend⟩ := waring8_from_seed_tables_conditional hseed hcoefficientSeed hsound
  refine ⟨η,hη,?_⟩
  intro P R W core pruning minor hP hW hR hpartition c hc hcore Cf Cg hCf hCg hF hg C₀ hC₀ hm
  have hA := hpartition.mono (fun _ hn => pruning_subset_period hn)
  exact hend P R core pruning minor hP hR hpartition c hc hcore
    (pruning8_isLittleO P R W pruning hP hW hCf hCg hA hF hg) C₀ hC₀ hm

/-- Degree nine needs no additional smooth source moment for pruning, because
the pointwise trivial smooth bound and ordinary 11th moment suffice. -/
theorem waring9_from_source_estimates
    (hseed : AdmissibleCurve 9 source9)
    (hcoefficientSeed : AdmissibleCurve 18 coefficientSource9)
    (hsound : ∀ i, i < policies9.size → AnalyticPolicySound 9 policies9[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R W : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop → Tendsto W atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n^η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*(P n)^(37 : ℝ) ≤
          arcContribution 9 11 35 (P n) (R n) n (core n)) →
        ∀ Cf : ℝ, 0 < Cf →
        (∀ᶠ n in atTop, ordinaryArcMoment 9 11 (P n) (pruning n) ≤
          ENNReal.ofReal (Cf*(P n)^2*(W n)^(-(1/18 : ℝ)))) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 9 90 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(80+epsilon9)) →
        WaringBound 9 46 := by
  obtain ⟨η,hη,hend⟩ := waring9_from_seed_tables_conditional hseed hcoefficientSeed hsound
  refine ⟨η,hη,?_⟩
  intro P R W core pruning minor hP hW hR hpartition c hc hcore Cf hCf hF C₀ hC₀ hm
  exact hend P R core pruning minor hP hR hpartition c hc hcore
    (pruning9_isLittleO P R W pruning hP hW hCf hF) C₀ hC₀ hm

#print axioms waring8_from_source_estimates
#print axioms waring9_from_source_estimates
end Waring.EndgameFromPublishedInputs
