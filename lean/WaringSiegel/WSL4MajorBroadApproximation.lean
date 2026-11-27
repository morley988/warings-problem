import WaringSiegel.WSL4MajorPruning
import WaringSiegel.WSL4MajorGroupedApproximation

/-! # The original broad major coefficient and its actual grouped main term -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem broadSmoothCoefficient_grouped_main_error
    (k n : ℕ) (hk : 3≤k) (hn : 1≤n)
    (hvariables : Thresholds.sufficientVariables k≤(n:ℤ))
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (δ : ℝ) (hδ : 0≤δ) :
    ∃ a C₀ η : ℝ, 0<a ∧ a<1 ∧ 0<C₀ ∧ 0<η ∧
      ∀ N : ℕ, ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧
      ∀ (target : 𝓞 K) (htarget : target≠0) (M : ℝ),
      Summable (fun I : {I : Ideal (𝓞 K) // I≠0} =>
        (I.1.absNorm:ℝ)^δ*‖idealPrimitivePowerCoefficient k n I.1 I.2 target‖) →
      (∑' I : {I : Ideal (𝓞 K) // I≠0},
        (I.1.absNorm:ℝ)^δ*‖idealPrimitivePowerCoefficient k n I.1 I.2 target‖)≤M →
      let P := rootScale k target
      let X := P^finrank ℚ K
      let L := (k:ℝ)^finrank ℚ K*X^a
      1≤L → L≤X →
      (2:ℝ)^finrank ℚ K*L^2<(FractionalIdeal.absNorm (inverseDifferent K):ℝ)*(P^k)^finrank ℚ K →
      ‖smoothRootMajorCoefficient k n ρ R hρ hR target htarget-
        (majorScale (K := K) k n P:ℂ)*
          (powerIdealSingularSeries k n target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k n
              (smoothRootWeight ρ R) (normalizedTarget k 1 target))‖ ≤
        C₀*X^((n:ℝ)-k-η)+
          (C₁*P^(finrank ℚ K*n)*(L/X)^N*(1+L/X)+
            majorScale (K := K) k n P*C₂*M/L^δ) := by
  obtain ⟨a,C₀,η,ha0,ha1,hC₀,hη,hprune⟩ :=
    compactTraceWeylSum_shrinking_pruning (K := K)
      (smoothWeightSchwartz ρ R hρ hR) (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
      k n hk hvariables
  refine ⟨a,C₀,η,ha0,ha1,hC₀,hη,?_⟩
  intro N
  obtain ⟨C₁,C₂,hC₁,hC₂,herror⟩ := narrowSmoothCoefficient_grouped_main_error (K := K)
    k (n-1) (by omega) ρ R hρ hR δ hδ N
  have hn1 : n-1+1=n := Nat.sub_add_cancel hn
  simp only [hn1] at herror
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro target htarget M hs hb P X L hL hLX hsep
  have hp := hprune P (one_le_rootScale htarget k) target
  change ‖smoothRootMajorCoefficient k n ρ R hρ hR target htarget-
    cutoffSmoothCoefficient k n ρ R hρ hR L target htarget‖≤_ at hp
  have he := herror target htarget M hs hb L hL hLX hsep
  have ht := norm_add_le
    (smoothRootMajorCoefficient k n ρ R hρ hR target htarget-
      cutoffSmoothCoefficient k n ρ R hρ hR L target htarget)
    (cutoffSmoothCoefficient k n ρ R hρ hR L target htarget-
      (majorScale (K := K) k n P:ℂ)*
        (powerIdealSingularSeries k n target *
          pairedWeightedSingularIntegral (integerLatticeSourceScale K) k n
            (smoothRootWeight ρ R) (normalizedTarget k 1 target)))
  rw [sub_add_sub_cancel] at ht
  exact ht.trans (add_le_add hp he)

#print axioms broadSmoothCoefficient_grouped_main_error
end WaringSiegel.WSL4
