import WaringSiegel.WSL4ArchCenterMass
import WaringSiegel.WSL4MajorCubicTail

/-! # Uniform eighth-kappa mass for the actual rational centers -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceRationalCenters_kappa_eighth_weight_sum_le
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (N : ℕ) (t : ℝ) :
    letI := Fintype.ofFinite (traceRationalCenters K N)
    (∑ q : traceRationalCenters K N,
      ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)^t *
        cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^8) ≤
      ∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1:ℝ)^(1+t)*cubicKappa B I^8 := by
  have hh := traceRationalCenters_nonneg_weight_sum_le N
    (fun I => (Ideal.absNorm I:ℝ)^t*cubicKappaIdeal B I^8) (fun I => by positivity)
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  have hN : 0<(Ideal.absNorm I.1:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)
  rw [Real.rpow_add hN,Real.rpow_one]
  simp only [cubicKappaIdeal_coe]
  ring

theorem traceRationalCenters_kappa_eighth_five_fourths_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0≤B v) :
    ∃ M : ℝ, 0<M ∧ ∀ N : ℕ,
      letI := Fintype.ofFinite (traceRationalCenters K N)
      (∑ q : traceRationalCenters K N,
        ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)^((5:ℝ)/4) *
          cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^8) ≤ M := by
  let f := fun I : {I : Ideal (𝓞 K) // I≠0} =>
    (Ideal.absNorm I.1:ℝ)^((9:ℝ)/4)*cubicKappa B I^8
  have hs : Summable f := cubicKappa_eighth_weighted_summable B hB (9/4) (by norm_num)
  have hf : ∀ I,0≤f I := fun I => by dsimp [f]; positivity
  have ht : 0≤∑' I,f I := tsum_nonneg hf
  refine ⟨(∑' I,f I)+1,by positivity,fun N => ?_⟩
  have hb := traceRationalCenters_kappa_eighth_weight_sum_le B N (5/4)
  norm_num only [show (1:ℝ)+5/4=9/4 by norm_num] at hb
  exact (hb.trans (hs.sum_le_tsum (cubicConductorCutoff N) (fun I _ => hf I))).trans
    (by linarith)

theorem cubicPruning_kappa_integral_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0≤B v)
    (C0 : ℝ) (hC0 : 1≤C0) :
    ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, ∀ X Y L : ℝ, 0<X → 0≤Y → 0<L →
      letI := Fintype.ofFinite (traceRationalCenters K N)
      (∑ q : traceRationalCenters K N,
        cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^8 *
          ∫ β in cubicPruningRegion (K := K)
            ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ) X L C0,
            cubicPruningKernel ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ)
              X Y β ∂archimedeanDualMeasure (integerLatticeSourceScale K)) ≤
        C*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) := by
  obtain ⟨C,hC,hbound⟩ := cubicPruning_finite_weighted_bound (K := K) C0 hC0
  obtain ⟨M,hM,hmass⟩ := traceRationalCenters_kappa_eighth_five_fourths_bound B hB
  refine ⟨C*M,mul_pos hC hM,?_⟩
  intro N X Y L hX hY hL
  letI := Fintype.ofFinite (traceRationalCenters K N)
  apply hbound
    (fun q : traceRationalCenters K N =>
      ((traceConductor (traceCenterRepresentative q)).absNorm:ℝ))
    (fun q => cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))^8)
    (fun q => Nat.cast_pos.mpr
      (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero (traceCenterRepresentative q)))
    (fun _ => by positivity) X Y L M hX hY hL
  exact hmass N

#print axioms traceRationalCenters_kappa_eighth_five_fourths_bound
#print axioms cubicPruning_kappa_integral_bound
end WaringSiegel.WSL4
