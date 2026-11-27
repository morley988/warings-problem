import WaringSiegel.WSL4ArchFourthUnion
import WaringSiegel.WSL3PoissonMajorFourthKappa
import WaringSiegel.WSL3CubicKappaTruncation

/-! # The actual near-zero product-weight major-fourth bound, with exactly the finite twisted gap

All prime-power weight summability, ideal counting, quotient projection,
stationary-kernel integration, and scale normalization are proved here or
in imports. The remaining hypothesis is the literal finite twisted complete
cubic sum estimate. The analytic source is the actual near-zero mixed h-weight.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

/-- The W^(1+epsilon) bound for the genuine projected major arcs and genuine
near-zero product sum. Only the displayed finite twisted sum estimate is
retained as an unproved arithmetic premise. -/
theorem nearZeroTraceCubicSum_major_fourth
    (L : ℝ) (hL : 1 ≤ L)
    (ε : ℝ) (hε : 0 < ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v, 0 ≤ B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in traceMajorArcUnion (K := K) (P^3) (L*P^finrank ℚ K),
        ‖nearZeroTraceCubicSum (K := K) P (by linarith) q‖^4 ∂traceHaar) ≤
          C*(P^finrank ℚ K : ℝ)^(1+ε) := by
  obtain ⟨A,hA,hbound⟩ := cubicKappa_fourth_norm_truncation_bound B hB ε hε
  refine nearZeroTraceCubicSum_major_fourth_of_weight_bound L hL ε hε
    (cubicKappaIdeal B) (cubicKappaIdeal_nonneg B hB) ?_ A hA ?_
  · intro γ ξ
    have hne : traceConductor γ ≠ 0 := traceConductor_ne_zero γ
    simpa only [cubicKappaIdeal,dif_neg hne] using hfinite γ ξ
  · intro N hN
    have hcut : ∀ I ∈ cubicConductorCutoff (K := K) N, (Ideal.absNorm I.1 : ℝ) ≤ N := by
      intro I hI
      exact_mod_cast (mem_cubicConductorCutoff N I).mp hI
    simpa only [cubicKappaIdeal_coe] using hbound (N:ℝ) (by exact_mod_cast hN)
      (cubicConductorCutoff N) hcut

end WaringSiegel.WSL4
#print axioms WaringSiegel.WSL4.nearZeroTraceCubicSum_major_fourth
