import WaringSiegel.WSL4LocalPowerDensityError
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # Convergence and uniform positivity of the actual power-density Euler product

The factors are limits of the actual finite quotient solution counts. No
existence assumption on local densities or on an infinite product is used.
Identification with the conductor character series is a separate statement.
-/
noncomputable section
open IsLocalRing Filter Topology
open scoped NumberField BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

def powerDensityEulerProduct (k p : ℕ) (ν : 𝓞 K) : ℝ :=
  ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), completionPowerDensity v k p ν

theorem completionPowerDensity_multipliable
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p)
    {ν : 𝓞 K} (hν : ν≠0) :
    Multipliable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      completionPowerDensity v k p ν) := by
  have h := multipliable_one_add_of_summable
    (show Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      ‖completionPowerDensity v k p ν-1‖) by
      simpa only [Real.norm_eq_abs] using completionPowerDensity_error_summable k p hk hp hkp hν)
  simpa only [add_sub_cancel] using h

theorem hasProd_completionPowerDensity
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p)
    {ν : 𝓞 K} (hν : ν≠0) :
    HasProd (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      completionPowerDensity v k p ν) (powerDensityEulerProduct k p ν) :=
  (completionPowerDensity_multipliable k p hk hp hkp hν).hasProd

theorem powerDensityEulerProduct_nonneg
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p)
    {ν : 𝓞 K} (hν : ν≠0) : 0≤powerDensityEulerProduct k p ν := by
  apply ge_of_tendsto (hasProd_completionPowerDensity k p hk hp hkp hν)
  apply Filter.Eventually.of_forall
  intro S
  apply Finset.prod_nonneg
  intro v hv
  apply ge_of_tendsto (tendsto_completionPowerDensity v k p hk (by omega) hν)
  exact Filter.Eventually.of_forall (fun e => by unfold normalizedLocalPowerCount; positivity)

theorem powerDensityEulerProduct_uniform_positive
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p) :
    ∃ c : ℝ,0<c ∧ ∀ ν : 𝓞 K,ν≠0 → LocalUnitSolvable k p ν →
      c≤powerDensityEulerProduct k p ν := by
  obtain ⟨c,hc,hprod⟩ := actual_power_densities_finite_products_uniform_positive (K:=K) k p hk hp
  refine ⟨c,hc,fun ν hν hlocal => ?_⟩
  apply ge_of_tendsto (hasProd_completionPowerDensity k p hk hp hkp hν)
  exact Filter.Eventually.of_forall (hprod ν hν hlocal)

theorem powerDensityEulerProduct_pos
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p)
    {ν : 𝓞 K} (hν : ν≠0) (hlocal : LocalUnitSolvable k p ν) :
    0<powerDensityEulerProduct k p ν := by
  obtain ⟨c,hc,hbound⟩ := powerDensityEulerProduct_uniform_positive (K:=K) k p hk hp hkp
  exact hc.trans_le (hbound ν hν hlocal)

#print axioms completionPowerDensity_multipliable
#print axioms hasProd_completionPowerDensity
#print axioms powerDensityEulerProduct_uniform_positive
end WaringSiegel.WSL4Local
