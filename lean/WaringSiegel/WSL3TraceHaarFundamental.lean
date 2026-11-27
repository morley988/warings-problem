import WaringSiegel.WSL3IdealPoissonMeasure
import WaringSiegel.WSL2TraceHaar
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-! # WSL3: actual trace Haar measure from the normalized dual fundamental domain

This identifies the probability Haar measure used in Fourier extraction
with the quotient pushforward of the actual paired trace-frequency measure.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding
open WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical Pointwise
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem traceDualFundamentalDomain_isAddFundamentalDomain :
    IsAddFundamentalDomain (archInverseDifferentLattice (K := K)).toAddSubgroup.op
      (ZSpan.fundamentalDomain (archimedeanTraceDualBasis (K := K)))
      (archimedeanDualMeasure (integerLatticeSourceScale K)) := by
  let Γ := (archInverseDifferentLattice (K := K)).toAddSubgroup
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  have h := ZSpan.isAddFundamentalDomain' (archimedeanTraceDualBasis (K := K)) μ
  change IsAddFundamentalDomain Γ _ μ at h
  exact h.preimage_of_equiv (MeasurePreserving.id μ).quasiMeasurePreserving
    (AddSubgroup.equivOp Γ).bijective (by intro g x; change x + g.1 = g.1 + x; exact add_comm _ _)

theorem traceHaar_eq_quotient_fundamentalDomain :
    traceHaar (K := K) =
      Measure.map (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K)
        ((archimedeanDualMeasure (integerLatticeSourceScale K)).restrict
          (ZSpan.fundamentalDomain (archimedeanTraceDualBasis (K := K)))) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  let Γ := (archInverseDifferentLattice (K := K)).toAddSubgroup
  let D := ZSpan.fundamentalDomain (archimedeanTraceDualBasis (K := K))
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  letI : Countable Γ := by
    change Countable (Submodule.span ℤ (Set.range (archimedeanTraceDualBasis (K := K))))
    infer_instance
  let π : mixedSpace K →+ ArchimedeanTraceTorus K :=
    (archInverseDifferentLattice (K := K)).mkQ.toAddMonoidHom
  have hπ : Measurable π := continuous_quotient_mk'.measurable
  have hD : IsAddFundamentalDomain Γ D μ :=
    ZSpan.isAddFundamentalDomain' (archimedeanTraceDualBasis (K := K)) μ
  have hDm : μ D = 1 := integerLatticeDualMeasure_fundamentalDomain
  let μ' : Measure (ArchimedeanTraceTorus K) := Measure.map π (μ.restrict D)
  letI : IsProbabilityMeasure μ' := by
    constructor
    change (Measure.map π (μ.restrict D)) Set.univ = 1
    rw [Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hDm]
  letI : Measure.IsAddLeftInvariant μ' := by
    constructor
    intro q
    obtain ⟨θ,rfl⟩ := Quotient.exists_rep q
    ext U hU
    rw [Measure.map_apply (measurable_const_add _) hU]
    change (Measure.map π (μ.restrict D)) ((fun x => π θ + x) ⁻¹' U) =
      (Measure.map π (μ.restrict D)) U
    rw [Measure.map_apply hπ (hU.preimage (measurable_const_add _)),
      Measure.map_apply hπ hU,
      Measure.restrict_apply (hπ (hU.preimage (measurable_const_add _))),
      Measure.restrict_apply (hπ hU)]
    have hset : π ⁻¹' ((fun x => π θ + x) ⁻¹' U) ∩ D =
        (fun x => θ + x) ⁻¹' ((π ⁻¹' U) ∩ ((fun x => θ + x) '' D)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, map_add, Set.mem_image]
      constructor
      · rintro ⟨hu,hx⟩
        exact ⟨hu,x,hx,rfl⟩
      · rintro ⟨hu,y,hy,hxy⟩
        have he : y = x := add_left_cancel hxy
        exact ⟨hu,he ▸ hy⟩
    rw [hset, measure_preimage_add]
    have ht : IsAddFundamentalDomain Γ ((fun x => θ + x) '' D) μ := by
      simpa only [Set.image_vadd] using hD.vadd_of_comm θ
    apply ht.measure_set_eq hD (hπ hU)
    intro g
    ext x
    have hg : π g.1 = 0 :=
      (Submodule.Quotient.mk_eq_zero (archInverseDifferentLattice (K := K))).mpr g.2
    change π (g.1 + x) ∈ U ↔ π x ∈ U
    rw [map_add, hg, zero_add]
  have he := isAddInvariant_eq_smul_of_compactSpace μ' (traceHaar (K := K))
  have hscale : addHaarScalarFactor μ' (traceHaar (K := K)) = 1 := by
    have hu := congrArg (fun m : Measure (ArchimedeanTraceTorus K) => m Set.univ) he
    simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hu
    exact_mod_cast hu.symm
  rw [hscale, one_smul] at he
  exact he.symm

theorem traceHaar_projection_measurePreserving :
    MeasurePreserving (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K)
      ((archimedeanDualMeasure (integerLatticeSourceScale K)).restrict
        (ZSpan.fundamentalDomain (archimedeanTraceDualBasis (K := K))))
      (traceHaar (K := K)) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  exact ⟨continuous_quotient_mk'.measurable, traceHaar_eq_quotient_fundamentalDomain.symm⟩

theorem traceHaar_integral_fundamentalDomain
    (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f) :
    (∫ q, f q ∂traceHaar) =
      ∫ x in ZSpan.fundamentalDomain (archimedeanTraceDualBasis (K := K)),
        f (Submodule.Quotient.mk x) ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  rw [traceHaar_eq_quotient_fundamentalDomain]
  exact integral_map traceHaar_projection_measurePreserving.measurable.aemeasurable
    hf.aestronglyMeasurable

end WaringSiegel
#print axioms WaringSiegel.traceHaar_eq_quotient_fundamentalDomain
#print axioms WaringSiegel.traceHaar_integral_fundamentalDomain
