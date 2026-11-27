import WaringSiegel.WSL3AuxiliaryIdealProducts

/-! # WSL3: the auxiliary-prime finite factors cost only the square of their radical norm -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem primePowerMaskedConductorMass_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r e : ℕ) (p ν : 𝓞 K) (t : ℝ) :
    0 ≤ primePowerMaskedConductorMass v r e p ν t := by
  unfold primePowerMaskedConductorMass
  split_ifs
  · exact idealMaskedConductorMass_nonneg _ _ _ _ _ _ _
  · exact le_rfl

theorem primePowerMaskedConductorMass_le_square
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 173 ≤ Ideal.absNorm v.asIdeal)
    (r e : ℕ) (he : 1 ≤ e) (her : e ≤ r) (p ν : 𝓞 K) (hpv : p ∈ v.asIdeal) :
    primePowerMaskedConductorMass v r e p ν (5/4 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)^2 := by
  cases r with
  | zero => omega
  | succ n =>
    simp only [primePowerMaskedConductorMass, dif_pos her, idealMaskedConductorMass]
    exact prime_power_masked_weighted_mass_le_square v h6 hq n e he her p ν hpv

theorem idealMaskedConductorMass_bad_product_le
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (he : ∀ v ∈ S, 1 ≤ e v) (her : ∀ v ∈ S, e v ≤ r v)
    (h6 : ∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal)
    (hq : ∀ v ∈ S, 173 ≤ Ideal.absNorm v.asIdeal)
    (p ν : 𝓞 K) (hpv : ∀ v ∈ S, p ∈ v.asIdeal) :
    idealMaskedConductorMass (∏ v ∈ S, v.asIdeal^r v) (prime_power_product_ne_zero S r)
      (∏ v ∈ S, v.asIdeal^e v) (prime_power_product_le S r e her) p ν (5/4 : ℝ) ≤
      ∏ v ∈ S, (Ideal.absNorm v.asIdeal : ℝ)^2 := by
  rw [idealMaskedConductorMass_finset_prod S r e her p ν (5/4 : ℝ)]
  apply Finset.prod_le_prod
    (fun v _ => primePowerMaskedConductorMass_nonneg v (r v) (e v) p ν (5/4 : ℝ))
  intro v hv
  exact primePowerMaskedConductorMass_le_square v (h6 v hv) (hq v hv)
    (r v) (e v) (he v hv) (her v hv) p ν (hpv v hv)

theorem idealMaskedConductorMass_good_bad_product_le
    (J : Ideal (𝓞 K)) (hJ : J ≠ 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (r e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ)
    (he : ∀ v ∈ S, 1 ≤ e v) (her : ∀ v ∈ S, e v ≤ r v)
    (h6 : ∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal)
    (hq : ∀ v ∈ S, 173 ≤ Ideal.absNorm v.asIdeal)
    (hcop : IsCoprime J (∏ v ∈ S, v.asIdeal^r v))
    (p ν : 𝓞 K) (hpJ : IsUnit (Ideal.Quotient.mk J p))
    (hpv : ∀ v ∈ S, p ∈ v.asIdeal) :
    idealMaskedConductorMass (J * ∏ v ∈ S, v.asIdeal^r v)
      (mul_ne_zero hJ (prime_power_product_ne_zero S r))
      (∏ v ∈ S, v.asIdeal^e v)
      (Ideal.mul_le_left.trans (prime_power_product_le S r e her)) p ν (5/4 : ℝ) ≤
      cubicSharpUniformSingularSeriesConstant K * ∏ v ∈ S, (Ideal.absNorm v.asIdeal : ℝ)^2 := by
  have hprod := idealMaskedConductorMass_mul J (∏ v ∈ S, v.asIdeal^r v) ⊤
    (∏ v ∈ S, v.asIdeal^e v) hJ (prime_power_product_ne_zero S r) hcop le_top
    (prime_power_product_le S r e her) p ν (5/4 : ℝ)
  have htop : (⊤ : Ideal (𝓞 K)) * (∏ v ∈ S, v.asIdeal^e v) =
      ∏ v ∈ S, v.asIdeal^e v := by rw [← Ideal.one_eq_top, one_mul]
  simp only [htop] at hprod
  rw [hprod]
  exact mul_le_mul (finiteMaskedConductorMass_unrestricted_le J hJ p ν hpJ)
    (idealMaskedConductorMass_bad_product_le S r e he her h6 hq p ν hpv)
    (idealMaskedConductorMass_nonneg _ _ _ _ _ _ _)
    cubicSharpUniformSingularSeriesConstant_pos.le

end WaringSiegel
#print axioms WaringSiegel.idealMaskedConductorMass_good_bad_product_le
