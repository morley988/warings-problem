import WaringSiegel.WSL2UnitPointwiseFourier

/-!
# A uniform positive continuous density for the actual normalized targets

Combining actual positive-unit balancing with the continuous density theorem
fixes the root box, density lower bound and neighborhood radius before every
nonzero totally positive algebraic-integer target. The unit is chosen only
after the target, exactly as required by the Waring–Siegel normalization.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical
open NumberField NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- Uniform archimedean positivity for the genuine normalized integer targets,
with s+2 roots. No compactness or analytic hypothesis remains. -/
theorem exists_uniform_normalized_target_density (k s : ℕ) (hk : 0 < k) :
    ∃ ρ R c δ : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧ 0 < δ ∧
      Continuous (continuousArchimedeanDensity (K := K) k s ρ R) ∧
      HasCompactSupport (continuousArchimedeanDensity (K := K) k s ρ R) ∧
      (volume.withDensity (fun x : mixedSpace K =>
        ENNReal.ofReal (continuousArchimedeanDensity k s ρ R x))) =
          archimedeanWaringMeasure (K := K) k (s+1) ρ R ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        ∀ b ∈ Metric.ball (normalizedTarget k u ν) δ,
          c ≤ continuousArchimedeanDensity k s ρ R b := by
  obtain ⟨B, hB, _, htargets⟩ := exists_compact_normalized_targets K k hk
  obtain ⟨ρ, R, hρ, hR, _, hcont, hmeasure, c, δ, hc, hδ, hlower⟩ :=
    exists_uniform_continuous_archimedean_density_lower (K := K) k s hk B (by linarith)
  refine ⟨ρ, R, c, δ, hρ, hR, hc, hδ, hcont,
    continuousArchimedeanDensity_hasCompactSupport k s hk ρ R hρ, hmeasure, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := htargets ν hν hp
  exact ⟨u, hu, hlower _ hb⟩

/-- In particular the actual eight-cube density is uniformly positive at
all normalized positive targets, with no local-solubility premise. -/
theorem exists_uniform_eight_cube_target_density :
    ∃ ρ R c : ℝ, 0 < ρ ∧ 0 < R ∧ 0 < c ∧
      Continuous (continuousArchimedeanDensity (K := K) 3 6 ρ R) ∧
      (volume.withDensity (fun x : mixedSpace K =>
        ENNReal.ofReal (continuousArchimedeanDensity 3 6 ρ R x))) =
          archimedeanWaringMeasure (K := K) 3 7 ρ R ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        c ≤ continuousArchimedeanDensity 3 6 ρ R (normalizedTarget 3 u ν) := by
  obtain ⟨ρ, R, c, δ, hρ, hR, hc, hδ, hcont, _, hm, ht⟩ :=
    exists_uniform_normalized_target_density (K := K) 3 6 (by norm_num)
  refine ⟨ρ, R, c, hρ, hR, hc, hcont, hm, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := ht ν hν hp
  exact ⟨u, hu, hb _ (Metric.mem_ball_self hδ)⟩

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_uniform_normalized_target_density
#print axioms WaringSiegel.WSL2.exists_uniform_eight_cube_target_density
