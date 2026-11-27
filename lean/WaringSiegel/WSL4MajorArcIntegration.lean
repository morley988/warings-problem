import WaringSiegel.WSL4MajorProjection
import WaringSiegel.WSL2TraceMajorArcUnion

/-! # Exact complex integration over separated actual major arcs

The conductor separation cutoff makes the quotient projection injective on
each lifted arc.  Consequently the actual finite union integral is the sum
of upstairs integrals in the paired dual measure, with no multiplicity loss.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.mixedEmbedding Module
  WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem quotient_injOn_productMajorArc
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K)
    (γ : K) :
    Set.InjOn (Submodule.Quotient.mk : mixedSpace K → ArchimedeanTraceTorus K)
      (productMajorArc (inverseDifferent K) H L γ) := by
  intro x hx y hy hxy
  by_contra hne
  have hxyLat : x-y ∈ archInverseDifferentLattice (K := K) :=
    (Submodule.Quotient.eq _).mp hxy
  obtain ⟨a,ha,hea⟩ := (mem_archInverseDifferentLattice _).mp hxyLat
  have ha0 : a ≠ 0 := by
    intro h
    have hz : x-y = 0 := by simpa only [h,map_zero] using hea.symm
    exact hne (sub_eq_zero.mp hz)
  have hcent : γ ≠ γ+a := by
    intro h
    exact ha0 (add_left_cancel (show γ+a = γ+0 by simpa using h.symm))
  have hγ' : x ∈ productMajorArc (inverseDifferent K) H L (γ+a) := by
    change (Ideal.absNorm (conductorIdeal (inverseDifferent K) (γ+a)) : ℝ) *
      productArcWeight H (x - mixedEmbedding K (γ+a)) ≤ L
    rw [conductorIdeal_add_lattice _ _ _ ha, map_add, hea]
    have he : x-(mixedEmbedding K γ+(x-y)) = y-mixedEmbedding K γ := by abel
    rw [he]
    exact hy
  exact Set.disjoint_left.mp
    (productMajorArcs_disjoint _ inverseDifferent_ne_zero H L hH hL hsmall γ (γ+a) hcent)
    hx hγ'

theorem traceMajorArc_integral_eq
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K)
    (γ : K) (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f) :
    (∫ q in traceMajorArc H L γ, f q ∂traceHaar) =
      ∫ x in productMajorArc (inverseDifferent K) H L γ,
        f (Submodule.Quotient.mk x)
        ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  exact traceHaar_integral_projected_eq _
    (productMajorArc_isCompact _ inverseDifferent_ne_zero H L hH γ)
    (quotient_injOn_productMajorArc H L hH hL hsmall γ) f hf

local instance centersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

theorem traceMajorArcUnion_integral_eq_sum
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K)
    (f : ArchimedeanTraceTorus K → ℂ) (hf : Continuous f) :
    (∫ q in traceMajorArcUnion (K := K) H L, f q ∂traceHaar) =
      ∑ q : traceRationalCenters K ⌊L⌋₊,
        ∫ x in productMajorArc (inverseDifferent K) H L (traceCenterRepresentative q),
          f (Submodule.Quotient.mk x)
          ∂archimedeanDualMeasure (integerLatticeSourceScale K) := by
  letI : MeasurableSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_measurableSpace
  letI : BorelSpace (ArchimedeanTraceTorus K) := archimedeanTraceTorus_borelSpace
  have hfint : Integrable f (traceHaar (K := K)) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [traceMajorArcUnion_eq_finite_union,
    integral_iUnion_fintype
      (fun q => traceMajorArc_measurableSet H L hH (traceCenterRepresentative q))
      (traceMajorArcUnion_pairwise_disjoint H L hH hL hsmall)
      (fun _ => hfint.integrableOn)]
  apply Finset.sum_congr rfl
  intro q hq
  exact traceMajorArc_integral_eq H L hH hL hsmall (traceCenterRepresentative q) f hf

#print axioms quotient_injOn_productMajorArc
#print axioms traceMajorArcUnion_integral_eq_sum
end WaringSiegel.WSL4
