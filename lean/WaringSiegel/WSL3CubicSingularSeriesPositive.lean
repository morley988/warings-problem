import WaringSiegel.WSL3CubicSingularSeries

/-! # WSL3: target-uniform positivity of the actual eight-cube singular series -/
noncomputable section
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem cubicSingularSeries_eq_density_product
    {ν : 𝓞 K} (hν : ν ≠ 0)
    (σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (hσ : ∀ v, Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 (σ v)))
    (hp : Multipliable σ) :
    cubicSingularSeries ν = ((∏' v, σ v : ℝ) : ℂ) := by
  have hm := hp.hasProd.map Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal
  have he : cubicConductorLocalFactor ν = fun v => (σ v : ℂ) := by
    funext v
    exact cubicConductorLocalFactor_eq_density v hν (hσ v)
  rw [(cubicSingularSeries_eq_euler_product hν).2, he]
  exact hm.tprod_eq

/-- One positive constant, chosen before the eligible nonzero target, bounds
the literal absolutely convergent character singular series from below. -/
theorem cubicSingularSeries_uniform_positive :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
        ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ∧
      (cubicSingularSeries ν).im = 0 ∧ c ≤ (cubicSingularSeries ν).re := by
  obtain ⟨c, hc, hbound⟩ := original_cubic_euler_product_uniform_positive (K := K)
  refine ⟨c, hc, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ, -, hp, hlower⟩ := hbound ν hν hν0
  have he := cubicSingularSeries_eq_density_product hν0 σ (fun v => (hσ v).2.2) hp
  refine ⟨idealPrimitiveCubicCoefficient_norm_summable hν0, ?_, ?_⟩
  · rw [he]
    rfl
  · rw [he]
    exact hlower

end WaringSiegel

#print axioms WaringSiegel.cubicSingularSeries_uniform_positive
