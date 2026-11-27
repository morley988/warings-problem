import WaringSiegel.WSL4PowerWeightedIdeal
import WaringSiegel.WSL4LocalPowerEulerProduct

/-! # The actual conductor-ordered power singular series and its positive density product -/
noncomputable section
set_option maxHeartbeats 1800000
open Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {K:Type*} [Field K] [NumberField K]

theorem idealPrimitivePowerCoefficient_norm_summable
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    Summable (fun I:{I:Ideal (𝓞 K)//I≠0} => ‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖) := by
  apply (idealPrimitivePowerCoefficient_norm_root_uniform_bound k p hk hp hkp ν).1.of_nonneg_of_le
    (fun I => norm_nonneg _)
  intro I
  have hI:1≤(Ideal.absNorm I.1:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp I.2)
  exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow hI (by positivity))

theorem primePowerPrimitivePowerCoefficient_pair_norm_summable
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    Summable (fun ve:IsDedekindDomain.HeightOneSpectrum (𝓞 K)×ℕ =>
      ‖primePowerPrimitivePowerCoefficient k p ve.1 (ve.2+1) ν‖) := by
  apply (weightedLocalPowerCoefficient_global_summable k p hk hp hkp ν).of_nonneg_of_le
    (fun ve => norm_nonneg _)
  intro ve
  apply le_mul_of_one_le_left (norm_nonneg _)
  apply one_le_pow₀
  have h:1≤(Ideal.absNorm ve.1.asIdeal:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp ve.1.ne_bot)
  exact h

theorem primePowerPrimitivePowerCoefficient_norm_summable
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ν:𝓞 K) :
    Summable (fun e:ℕ => ‖primePowerPrimitivePowerCoefficient k p v (e+1) ν‖) := by
  have h:=primePowerPrimitivePowerCoefficient_pair_norm_summable k p hk hp hkp ν
  exact h.prod_factor v

theorem powerLocalCoefficientSum_norm_summable
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    Summable (fun v:IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      ‖∑' e:ℕ,primePowerPrimitivePowerCoefficient k p v (e+1) ν‖) := by
  apply (primePowerPrimitivePowerCoefficient_pair_norm_summable k p hk hp hkp ν).prod.of_nonneg_of_le
    (fun v => norm_nonneg _)
  intro v
  exact norm_tsum_le_tsum_norm (primePowerPrimitivePowerCoefficient_norm_summable k p hk hp hkp v ν)

def powerConductorLocalFactor (k p:ℕ) (ν:𝓞 K)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℂ :=
  1+∑' e:ℕ,primePowerPrimitivePowerCoefficient k p v (e+1) ν

theorem powerConductorLocalFactor_eq_density
    (k p:ℕ) (hk:0<k) (hp:2≤p)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν:𝓞 K} (hν:ν≠0) :
    powerConductorLocalFactor k p ν v=(completionPowerDensity v k p ν:ℂ) := by
  rw [powerConductorLocalFactor,(primePowerPrimitivePowerCoefficient_hasSum k p hk hp v hν).tsum_eq]
  ring

theorem idealPrimitivePowerCoefficient_configuration (k p:ℕ) (hp:1≤p)
    (c:ConductorConfiguration K) (ν:𝓞 K) :
    idealPrimitivePowerCoefficient k p (configurationIdeal c).1 (configurationIdeal c).2 ν=
      ∏ v:c.1,primePowerPrimitivePowerCoefficient k p v.1 (c.2 v+1) ν := by
  rw [configurationIdeal,idealPrimitivePowerCoefficient_finset_prod k p hp]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro v hv
  simp only [configurationExponent,dif_pos v.2]

theorem powerIdealSingularSeries_eq_euler_product
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    Multipliable (powerConductorLocalFactor k p ν) ∧
      powerIdealSingularSeries k p ν=∏' v,powerConductorLocalFactor k p ν v := by
  let f:=fun v:IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    ∑' e:ℕ,primePowerPrimitivePowerCoefficient k p v (e+1) ν
  obtain ⟨hprod,heuler⟩:=complex_euler_finset_expansion f (powerLocalCoefficientSum_norm_summable k p hk hp hkp ν)
  refine ⟨hprod,?_⟩
  have hc:Summable (fun c:ConductorConfiguration K =>
      idealPrimitivePowerCoefficient k p (configurationIdeal c).1 (configurationIdeal c).2 ν) :=
    conductorConfigurationEquiv.summable_iff.mpr (idealPrimitivePowerCoefficient_norm_summable k p hk hp hkp ν).of_norm
  calc
    powerIdealSingularSeries k p ν=∑' c:ConductorConfiguration K,
      idealPrimitivePowerCoefficient k p (configurationIdeal c).1 (configurationIdeal c).2 ν :=
      (conductorConfigurationEquiv.tsum_eq (fun I => idealPrimitivePowerCoefficient k p I.1 I.2 ν)).symm
    _=∑' S:Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),∑' e:S→ℕ,
      idealPrimitivePowerCoefficient k p (configurationIdeal ⟨S,e⟩).1 (configurationIdeal ⟨S,e⟩).2 ν := hc.tsum_sigma
    _=∑' S:Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),∏ v∈S,f v := by
      apply tsum_congr
      intro S
      simp only [idealPrimitivePowerCoefficient_configuration k p (by omega)]
      rw [(complex_finite_product_hasSum S (fun v e => primePowerPrimitivePowerCoefficient k p v.1 (e+1) ν)
        (fun v => primePowerPrimitivePowerCoefficient_norm_summable k p hk hp hkp v.1 ν)).2.tsum_eq]
      exact Finset.prod_coe_sort S f
    _=∏' v,powerConductorLocalFactor k p ν v := heuler.symm

theorem powerIdealSingularSeries_eq_density_product
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) {ν:𝓞 K} (hν:ν≠0) :
    powerIdealSingularSeries k p ν=(powerDensityEulerProduct k p ν:ℂ) := by
  have hm:HasProd (fun v:IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (completionPowerDensity v k p ν:ℂ))
      (powerDensityEulerProduct k p ν:ℂ) :=
    (hasProd_completionPowerDensity k p hk (by omega) (by omega) hν).map
      Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal
  have he:powerConductorLocalFactor k p ν=fun v => (completionPowerDensity v k p ν:ℂ) := by
    funext v
    exact powerConductorLocalFactor_eq_density k p hk (by omega) v hν
  rw [(powerIdealSingularSeries_eq_euler_product k p hk hp hkp ν).2,he]
  exact hm.tprod_eq

theorem powerIdealSingularSeries_uniform_positive
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) :
    ∃ c:ℝ,0<c ∧ ∀ ν:𝓞 K,ν≠0 →LocalUnitSolvable k p ν →
      Summable (fun I:{I:Ideal (𝓞 K)//I≠0} => ‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖) ∧
        (powerIdealSingularSeries k p ν).im=0 ∧ c≤(powerIdealSingularSeries k p ν).re := by
  obtain ⟨c,hc,hbound⟩:=powerDensityEulerProduct_uniform_positive (K:=K) k p hk (by omega) (by omega)
  refine ⟨c,hc,fun ν hν hlocal => ?_⟩
  have he:=powerIdealSingularSeries_eq_density_product k p hk hp hkp hν
  refine ⟨idealPrimitivePowerCoefficient_norm_summable k p hk hp hkp ν,?_,?_⟩
  · rw [he]
    rfl
  · rw [he]
    exact hbound ν hν hlocal

#print axioms powerIdealSingularSeries_eq_euler_product
#print axioms powerIdealSingularSeries_eq_density_product
#print axioms powerIdealSingularSeries_uniform_positive
end WaringSiegel.WSL4Local
