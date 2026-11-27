import WaringSiegel.WSL4PowerUniformMass
import WaringSiegel.WSL4PowerIdealCoefficient

/-! # A uniform weighted absolute bound for actual conductor-ideal coefficients -/
noncomputable section
set_option maxHeartbeats 1600000
open Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {K:Type*} [Field K] [NumberField K]

def powerIdealConductorWeight (k:ℕ) (I:{I:Ideal (𝓞 K)//I≠0}) : ℝ :=
  ∏ ve∈nonzeroIdealConductorGraph I,powerPrimeConductorWeight k ve.1 ve.2

theorem powerIdealConductorWeight_nonneg (k:ℕ) (I:{I:Ideal (𝓞 K)//I≠0}) :
    0≤powerIdealConductorWeight k I := by
  apply Finset.prod_nonneg
  intro ve hve
  unfold powerPrimeConductorWeight
  positivity

theorem powerPrimeConductorWeight_pow (k:ℕ) (hk:0<k)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e:ℕ) :
    (Ideal.absNorm v.asIdeal:ℝ)^(e+1)≤powerPrimeConductorWeight k v e^k := by
  have hq1:1≤(Ideal.absNorm v.asIdeal:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  unfold powerPrimeConductorWeight
  rw [← pow_mul]
  apply pow_le_pow_right₀ hq1
  have hmod:=Nat.mod_lt e hk
  have he:=Nat.mod_add_div e k
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (e/k) k]
  omega

theorem powerIdealConductorWeight_pow (k:ℕ) (hk:0<k) (I:{I:Ideal (𝓞 K)//I≠0}) :
    (Ideal.absNorm I.1:ℝ)≤powerIdealConductorWeight k I^k := by
  have hn:(Ideal.absNorm I.1:ℝ)=
      ∏ ve∈nonzeroIdealConductorGraph I,(Ideal.absNorm ve.1.asIdeal:ℝ)^(ve.2+1) := by
    have h:=congrArg (fun J:Ideal (𝓞 K) => (Ideal.absNorm J:ℝ)) (nonzeroIdealConductorGraph_product I)
    simpa only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] using h.symm
  rw [hn,powerIdealConductorWeight,← Finset.prod_pow]
  exact Finset.prod_le_prod (fun ve hve => by positivity)
    (fun ve hve => powerPrimeConductorWeight_pow k hk ve.1 ve.2)

theorem powerIdealConductorWeight_ge_norm_root (k:ℕ) (hk:0<k) (I:{I:Ideal (𝓞 K)//I≠0}) :
    (Ideal.absNorm I.1:ℝ)^(1/(k:ℝ))≤powerIdealConductorWeight k I := by
  have hkR:(0:ℝ)<k := by exact_mod_cast hk
  rw [one_div,Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (powerIdealConductorWeight_nonneg k I) hkR]
  simpa only [Real.rpow_natCast] using powerIdealConductorWeight_pow k hk I

theorem weighted_power_ideal_coefficient_eq_graph_product (k p:ℕ) (hp:1≤p)
    (I:{I:Ideal (𝓞 K)//I≠0}) (ν:𝓞 K) :
    powerIdealConductorWeight k I*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖=
      ∏ ve∈nonzeroIdealConductorGraph I,weightedLocalPowerCoefficient k p ve.1 ve.2 ν := by
  rw [idealPrimitivePowerCoefficient_eq_graph_product k p hp,norm_prod]
  exact (Finset.prod_mul_distrib :
    (∏ ve∈nonzeroIdealConductorGraph I,powerPrimeConductorWeight k ve.1 ve.2*
      ‖primePowerPrimitivePowerCoefficient k p ve.1 (ve.2+1) ν‖)=_).symm

def powerUniformSingularSeriesConstant (K:Type*) [Field K] [NumberField K] (k:ℕ) : ℝ :=
  Real.exp (∑' v:IsDedekindDomain.HeightOneSpectrum (𝓞 K),powerUniformLocalWeightedMass k v)

theorem powerUniformSingularSeriesConstant_pos (k:ℕ) : 0<powerUniformSingularSeriesConstant K k :=
  Real.exp_pos _

theorem idealPrimitivePowerCoefficient_weighted_uniform_bound
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    Summable (fun I:{I:Ideal (𝓞 K)//I≠0} => powerIdealConductorWeight k I*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖) ∧
      (∑' I:{I:Ideal (𝓞 K)//I≠0},powerIdealConductorWeight k I*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖)≤
        powerUniformSingularSeriesConstant K k := by
  let f:=fun ve:IsDedekindDomain.HeightOneSpectrum (𝓞 K)×ℕ => weightedLocalPowerCoefficient k p ve.1 ve.2 ν
  have hf:∀ ve,0≤f ve := fun ve => weightedLocalPowerCoefficient_nonneg k p ve.1 ve.2 ν
  have hs:Summable f := weightedLocalPowerCoefficient_global_summable k p hk hp hkp ν
  have hfin:=summable_finset_products_of_nonneg f hf hs
  have hi:=hfin.comp_injective (nonzeroIdealConductorGraph_injective (K:=K))
  have hsum:Summable (fun I:{I:Ideal (𝓞 K)//I≠0} =>
      powerIdealConductorWeight k I*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖) := by
    apply hi.congr
    intro I
    exact (weighted_power_ideal_coefficient_eq_graph_product k p (by omega) I ν).symm
  refine ⟨hsum,?_⟩
  calc
    _≤∑' S:Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)×ℕ),∏ ve∈S,f ve := by
      apply Summable.tsum_le_tsum_of_inj nonzeroIdealConductorGraph nonzeroIdealConductorGraph_injective
        (fun S hS => Finset.prod_nonneg (fun ve hve => hf ve))
        (fun I => (weighted_power_ideal_coefficient_eq_graph_product k p (by omega) I ν).le) hsum hfin
    _≤Real.exp (∑' ve,f ve) := tsum_finset_products_le_exp f hf hs
    _≤powerUniformSingularSeriesConstant K k :=
      Real.exp_le_exp.mpr (weightedLocalPowerCoefficient_global_tsum_le k p hk hp hkp ν)

theorem idealPrimitivePowerCoefficient_norm_root_uniform_bound
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    Summable (fun I:{I:Ideal (𝓞 K)//I≠0} =>
      (Ideal.absNorm I.1:ℝ)^(1/(k:ℝ))*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖) ∧
      (∑' I:{I:Ideal (𝓞 K)//I≠0},
        (Ideal.absNorm I.1:ℝ)^(1/(k:ℝ))*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖)≤
          powerUniformSingularSeriesConstant K k := by
  obtain ⟨hs,hb⟩:=idealPrimitivePowerCoefficient_weighted_uniform_bound k p hk hp hkp ν
  have hnonneg:∀ I:{I:Ideal (𝓞 K)//I≠0},0≤
      (Ideal.absNorm I.1:ℝ)^(1/(k:ℝ))*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖ := fun I => by positivity
  have hle:∀ I:{I:Ideal (𝓞 K)//I≠0},
      (Ideal.absNorm I.1:ℝ)^(1/(k:ℝ))*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖≤
        powerIdealConductorWeight k I*‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖ :=
    fun I => mul_le_mul_of_nonneg_right (powerIdealConductorWeight_ge_norm_root k hk I) (norm_nonneg _)
  have hn:=hs.of_nonneg_of_le hnonneg hle
  exact ⟨hn,(Summable.tsum_le_tsum hle hn hs).trans hb⟩

#print axioms idealPrimitivePowerCoefficient_weighted_uniform_bound
#print axioms idealPrimitivePowerCoefficient_norm_root_uniform_bound
end WaringSiegel.WSL4Local
