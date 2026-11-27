import WaringSiegel.WSL3PoissonMajorFourthProjection

/-! # Exact integration on injectively projected trace arcs

Injectivity removes the lattice multiplicity in fundamental-domain unfolding.
The conclusion is equality of restricted measures and complex integrals.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem traceHaar_lintegral_projected_eq
    (A : Set (mixedSpace K)) (hA : IsCompact A)
    (hinj : Set.InjOn (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) A)
    (f : ArchimedeanTraceTorus K → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q in (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) '' A,
      f q ∂traceHaar) =
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
  have hshift (g : Γ) (x : mixedSpace K) : π (g.1+x) = π x := by
    have hg : π g.1 = 0 :=
      (Submodule.Quotient.mk_eq_zero (archInverseDifferentLattice (K := K))).mpr g.2
    change Submodule.Quotient.mk (g.1+x) = (Submodule.Quotient.mk x : ArchimedeanTraceTorus K)
    rw [Submodule.Quotient.mk_add]
    change π g.1 + π x = π x
    rw [hg,zero_add]
  have hpoint (x : mixedSpace K) : (π '' A).indicator f (π x) = ∑' g : Γ, F (g.1+x) := by
    by_cases hx : π x ∈ π '' A
    · obtain ⟨y,hy,hyx⟩ := hx
      have hg : y-x ∈ Γ := (Submodule.Quotient.eq _).mp hyx
      let g : Γ := ⟨y-x,hg⟩
      have hterm : F (g.1+x) = f (π x) := by
        dsimp only [F,g]
        rw [sub_add_cancel,Set.indicator_of_mem hy,hyx]
      have hsingle : (∑' h : Γ, F (h.1+x)) = F (g.1+x) := by
        apply tsum_eq_single g
        intro h hh
        have hn : h.1+x ∉ A := by
          intro hm
          have he : h.1+x = y := hinj hm hy ((hshift h x).trans hyx.symm)
          apply hh
          apply Subtype.ext
          exact eq_sub_iff_add_eq.mpr he
        exact Set.indicator_of_notMem hn _
      rw [Set.indicator_of_mem (show π x ∈ π '' A from ⟨y,hy,hyx⟩),hsingle,hterm]
    · rw [Set.indicator_of_notMem hx]
      symm
      have hz (g : Γ) : F (g.1+x) = 0 := by
        apply Set.indicator_of_notMem
        intro hm
        exact hx ⟨g.1+x,hm,hshift g x⟩
      simp only [hz,tsum_zero]
  have hunfold : (∫⁻ x in D, ∑' g : Γ, F (g.1+x) ∂μ) = ∫⁻ x, F x ∂μ := by
    have hmeas (g : Γ) : AEMeasurable (fun x => F (g.1+x)) (μ.restrict D) :=
      (hF.comp (measurable_const_add g.1)).aemeasurable
    rw [lintegral_tsum hmeas]
    exact (hD.lintegral_eq_tsum'' F).symm
  have hImage : MeasurableSet (π '' A) := (hA.image hπ).measurableSet
  change (∫⁻ q in π '' A, f q ∂traceHaar) = ∫⁻ x in A, f (π x) ∂μ
  rw [← lintegral_indicator hImage,traceHaar_eq_quotient_fundamentalDomain]
  rw [lintegral_map (hf.indicator hImage) hπ.measurable]
  calc
    _ = ∫⁻ x in D, ∑' g : Γ, F (g.1+x) ∂μ := lintegral_congr hpoint
    _ = ∫⁻ x, F x ∂μ := hunfold
    _ = _ := lintegral_indicator hA.measurableSet _

theorem traceHaar_restrict_projected_eq_map
    (A : Set (mixedSpace K)) (hA : IsCompact A)
    (hinj : Set.InjOn (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) A) :
    (traceHaar (K := K)).restrict
        ((Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) '' A) =
      Measure.map (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K)
        ((archimedeanDualMeasure (integerLatticeSourceScale K)).restrict A) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  apply Measure.ext_of_lintegral
  intro f hf
  have hπ : Measurable (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) :=
    (show Continuous (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K)
      from continuous_quotient_mk').measurable
  rw [lintegral_map hf hπ]
  exact traceHaar_lintegral_projected_eq A hA hinj f hf

/-- Exact complex integration, with no positivity restriction on the
integrand, once the actual quotient map is injective on the upstairs set. -/
theorem traceHaar_integral_projected_eq
    (A : Set (mixedSpace K)) (hA : IsCompact A)
    (hinj : Set.InjOn (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) A)
    (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f) :
    (∫ q in (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) '' A,
      f q ∂traceHaar) =
    ∫ x in A, f (Submodule.Quotient.mk x)
      ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  rw [traceHaar_restrict_projected_eq_map A hA hinj]
  have hπ : Measurable (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K) :=
    (show Continuous (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K)
      from continuous_quotient_mk').measurable
  exact integral_map hπ.aemeasurable hf.aestronglyMeasurable

#print axioms traceHaar_restrict_projected_eq_map
#print axioms traceHaar_integral_projected_eq
end WaringSiegel.WSL4
