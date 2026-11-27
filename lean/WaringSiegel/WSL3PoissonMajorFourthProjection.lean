import WaringSiegel.WSL3TraceHaarFundamental
import WaringSiegel.WSL3PoissonMixedKMajor

/-! # Nonnegative integration over genuine projected trace arcs

Projection may overlap its lattice translates. Unfolding the actual dual
fundamental domain proves the required upper bound without assuming injectivity.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL3
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceHaar_lintegral_projected_le
    (A : Set (mixedSpace K)) (hA : IsCompact A)
    (f : ArchimedeanTraceTorus K → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q in (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) '' A,
      f q ∂traceHaar) ≤
    ∫⁻ x in A, f (Submodule.Quotient.mk x)
      ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  let Γ := (archInverseDifferentLattice (K := K)).toAddSubgroup
  let D := ZSpan.fundamentalDomain (archimedeanTraceDualBasis (K := K))
  let π : mixedSpace K → ArchimedeanTraceTorus K := Submodule.Quotient.mk
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  letI : Countable Γ := by
    change Countable (Submodule.span ℤ (Set.range (archimedeanTraceDualBasis (K := K))))
    infer_instance
  have hπ : Continuous π := continuous_quotient_mk'
  have hD : IsAddFundamentalDomain Γ D μ :=
    ZSpan.isAddFundamentalDomain' (archimedeanTraceDualBasis (K := K)) μ
  let F : mixedSpace K → ℝ≥0∞ := A.indicator (fun x => f (π x))
  have hF : Measurable F := (hf.comp hπ.measurable).indicator hA.measurableSet
  have hunfold : (∫⁻ x in D, ∑' g : Γ, F (g.1+x) ∂μ) = ∫⁻ x, F x ∂μ := by
    have hmeas (g : Γ) : AEMeasurable (fun x => F (g.1+x)) (μ.restrict D) :=
      (hF.comp (measurable_const_add g.1)).aemeasurable
    rw [lintegral_tsum hmeas]
    exact (hD.lintegral_eq_tsum'' F).symm
  have hpoint (x : mixedSpace K) : (π '' A).indicator f (π x) ≤ ∑' g : Γ, F (g.1+x) := by
    by_cases hx : π x ∈ π '' A
    · obtain ⟨y,hy,hyx⟩ := hx
      have hg : y-x ∈ Γ := (Submodule.Quotient.eq _).mp hyx
      let g : Γ := ⟨y-x,hg⟩
      have hterm : F (g.1+x) = f (π x) := by
        dsimp only [F,g]
        rw [sub_add_cancel,Set.indicator_of_mem hy,hyx]
      rw [Set.indicator_of_mem (show π x ∈ π '' A from ⟨y,hy,hyx⟩)]
      rw [← hterm]
      exact ENNReal.le_tsum g
    · rw [Set.indicator_of_notMem hx]
      exact zero_le _
  have hImage : MeasurableSet (π '' A) := (hA.image hπ).measurableSet
  change (∫⁻ q in π '' A, f q ∂traceHaar) ≤ ∫⁻ x in A, f (π x) ∂μ
  rw [← lintegral_indicator hImage, traceHaar_eq_quotient_fundamentalDomain]
  rw [lintegral_map (hf.indicator hImage) hπ.measurable]
  calc
    _ ≤ ∫⁻ x in D, ∑' g : Γ, F (g.1+x) ∂μ := lintegral_mono hpoint
    _ = ∫⁻ x, F x ∂μ := hunfold
    _ = _ := lintegral_indicator hA.measurableSet _

/-- The actual normalized torus arc integral is at most its upstairs
trace-dual integral, including every possible lattice overlap. -/
theorem traceHaar_integral_projected_le
    (A : Set (mixedSpace K)) (hA : IsCompact A)
    (f : ArchimedeanTraceTorus K → ℝ) (hf : Continuous f) (hfn : ∀ q, 0 ≤ f q) :
    (∫ q in (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) '' A,
      f q ∂traceHaar) ≤
    ∫ x in A, f (Submodule.Quotient.mk x)
      ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  let π : mixedSpace K → ArchimedeanTraceTorus K := Submodule.Quotient.mk
  have hi : IntegrableOn f (π '' A) traceHaar :=
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
  have hiA : IntegrableOn (fun x => f (π x)) A μ :=
    (hf.comp continuous_quotient_mk').continuousOn.integrableOn_compact hA
  have hb := traceHaar_lintegral_projected_le A hA (fun q => ENNReal.ofReal (f q))
    (ENNReal.measurable_ofReal.comp hf.measurable)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hfn),
    ← ofReal_integral_eq_lintegral_ofReal hiA (Filter.Eventually.of_forall (fun x => hfn (π x)))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun x => hfn (π x)))).mp hb

end WaringSiegel.WSL3Poisson
#print axioms WaringSiegel.WSL3Poisson.traceHaar_integral_projected_le
