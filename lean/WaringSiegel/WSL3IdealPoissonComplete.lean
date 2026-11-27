import WaringSiegel.WSL3IdealPoissonResidues

/-!
# Literal complete-sum factors in ideal Poisson summation

For every finite residue weight the exact integer-ring sum equals the dual
ideal Fourier series with the actual finite complete coefficient. No Fourier
summability or arithmetic Poisson identity is left as a hypothesis.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def idealCompleteTraceFactor (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)]
    (F : (𝓞 K ⧸ I) → ℂ) (ξ : mixedSpace K) : ℂ :=
  ∑ q : 𝓞 K ⧸ I, F q * archimedeanTraceCharacter ξ
    (mixedEmbedding K (idealResidueRepresentative I q:K))

theorem idealCompleteTraceFactor_norm_le (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)]
    (F : (𝓞 K ⧸ I) → ℂ) (ξ : mixedSpace K) :
    ‖idealCompleteTraceFactor I F ξ‖ ≤ ∑ q,‖F q‖ := by
  unfold idealCompleteTraceFactor
  exact (norm_sum_le _ _).trans_eq (by
    simp only [norm_mul,archimedeanTraceCharacter_norm,mul_one])

theorem traceFourier_integralIdealDual_summable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (f : 𝓢(mixedSpace K,ℂ)) :
    Summable (fun ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹) =>
      traceFourier f (mixedEmbedding K (ξ:K))) :=
  traceFourier_fractionalIdealDual_summable (integralIdealAsUnit I hI) f

theorem ideal_trace_phase_fourier_summable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (a : mixedSpace K) (f : 𝓢(mixedSpace K,ℂ)) :
    Summable (fun ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹) =>
      archimedeanTraceCharacter (mixedEmbedding K (ξ:K)) a *
        traceFourier f (mixedEmbedding K (ξ:K))) := by
  apply Summable.of_norm_bounded (traceFourier_integralIdealDual_summable I hI f).norm
  intro ξ
  simp only [norm_mul,archimedeanTraceCharacter_norm,one_mul,le_refl]

/-- Exact ideal Poisson expansion of an arbitrary actual residue-weighted
Schwartz sum, with a literal finite complete coefficient. -/
theorem poisson_ideal_residue_weight (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ) (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*f (mixedEmbedding K (x:K))) =
      ((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K)) *
            traceFourier f (mixedEmbedding K (ξ:K))) := by
  rw [schwartz_residue_decomposition]
  simp_rw [poisson_integralIdeal_coset I hI]
  let c : ℝ := ((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹
  have hs (q : 𝓞 K ⧸ I) : Summable
      (fun ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹) =>
        F q*(archimedeanTraceCharacter (mixedEmbedding K (ξ:K))
          (mixedEmbedding K (idealResidueRepresentative I q:K))*traceFourier f (mixedEmbedding K (ξ:K)))) :=
    (ideal_trace_phase_fourier_summable I hI _ f).mul_left (F q)
  calc
    _ = c • ∑ q : 𝓞 K ⧸ I,
        ∑' ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          F q*(archimedeanTraceCharacter (mixedEmbedding K (ξ:K))
            (mixedEmbedding K (idealResidueRepresentative I q:K))*traceFourier f (mixedEmbedding K (ξ:K))) := by
      simp only [Complex.real_smul,Finset.mul_sum,tsum_mul_left]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = c • ∑' ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ∑ q : 𝓞 K ⧸ I, F q*(archimedeanTraceCharacter (mixedEmbedding K (ξ:K))
          (mixedEmbedding K (idealResidueRepresentative I q:K))*traceFourier f (mixedEmbedding K (ξ:K))) := by
      congr 1
      exact (Summable.tsum_finsetSum (fun q _ => hs q)).symm
    _ = _ := by
      congr 1
      apply tsum_congr
      intro ξ
      simp only [idealCompleteTraceFactor,Finset.sum_mul,mul_assoc]

#print axioms poisson_ideal_residue_weight
end WaringSiegel.WSL3Poisson
