import WaringSiegel.WSL3AuxiliaryEulerTruncation
import WaringSiegel.WSL3AuxiliaryEulerSplit

/-! # The literal auxiliary singular series equals its modified local Euler product -/
noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

/-- The finite replacement relation survives the cofinal limit over actual
complete characters. No Euler identification is a premise. -/
theorem auxiliaryCubicSingularSeries_replacement_identity
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal)
    (σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (hσ : ∀ v, Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 (σ v))) :
    let P := Ideal.span ({p} : Set (𝓞 K))
    let hP : P ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp
    auxiliaryCubicSingularSeries p hp ν *
        (∏ v ∈ idealPrimeSupport P hP, (σ v : ℂ)) =
      cubicSingularSeries ν *
        (∏ v ∈ idealPrimeSupport P hP, (cubicModifiedResidueFactor v ν : ℂ)) := by
  let P := Ideal.span ({p} : Set (𝓞 K))
  have hP : P ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp
  let S := idealPrimeSupport P hP
  have hpv : ∀ v ∈ S, p ∈ v.asIdeal := by
    intro v hv
    exact (Ideal.span_singleton_le_iff_mem v.asIdeal).mp
      (Ideal.dvd_iff_le.mp ((mem_idealPrimeSupport_iff_dvd P hP v).mp hv))
  have hlocal : Tendsto (fun z : AuxiliaryEulerIndex K =>
      ∏ v ∈ S, (normalizedPrimePowerCubicCount v 8
        (idealPrimeExponent (auxiliaryEulerModulus p z) v) ν : ℂ)) atTop
      (𝓝 (∏ v ∈ S, (σ v : ℂ))) := by
    apply tendsto_finset_prod
    intro v hv
    exact (Complex.continuous_ofReal.tendsto (σ v)).comp
      ((hσ v).comp (auxiliaryEulerModulus_prime_exponent_tendsto p hp v (hpv v hv)))
  have hleft := (idealMaskedCubicSum_tendsto p hp ν
    (auxiliaryCubicCharacterContribution_norm_summable p hp ν hgood).of_norm).mul hlocal
  have hright := (idealOrdinaryCubicSum_tendsto p hp ν).mul_const
    (∏ v ∈ S, (cubicModifiedResidueFactor v ν : ℂ))
  have heq :
      (fun z : AuxiliaryEulerIndex K =>
        idealMaskedCubicSum (auxiliaryEulerModulus p z) (auxiliaryEulerModulus_ne_zero p hp z)
          P (auxiliaryEulerModulus_le_mask p z) p ν *
          ∏ v ∈ S, (normalizedPrimePowerCubicCount v 8
            (idealPrimeExponent (auxiliaryEulerModulus p z) v) ν : ℂ)) =
      (fun z : AuxiliaryEulerIndex K =>
        idealOrdinaryCubicSum (auxiliaryEulerModulus p z) (auxiliaryEulerModulus_ne_zero p hp z) ν *
          ∏ v ∈ S, (cubicModifiedResidueFactor v ν : ℂ)) := by
    funext z
    exact idealMaskedCubicSum_finite_replacement _ P
      (auxiliaryEulerModulus_ne_zero p hp z) hP (auxiliaryEulerModulus_le_mask p z) p ν rfl
      (fun v hv => (hgood v (hpv v hv)).1)
  change Tendsto (fun z : AuxiliaryEulerIndex K =>
    idealMaskedCubicSum (auxiliaryEulerModulus p z) (auxiliaryEulerModulus_ne_zero p hp z)
      P (auxiliaryEulerModulus_le_mask p z) p ν *
      ∏ v ∈ S, (normalizedPrimePowerCubicCount v 8
        (idealPrimeExponent (auxiliaryEulerModulus p z) v) ν : ℂ)) atTop _ at hleft
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

theorem finite_replacement_product_formula {ι : Type*}
    (σ ρ : ι → ℝ) (S : Finset ι) (hσ : Multipliable σ) (hσ0 : ∀ i, σ i ≠ 0) :
    (∏' i, if i ∈ S then ρ i else σ i) =
      (∏' i, σ i) * (∏ i ∈ S, ρ i / σ i) := by
  let u : ι → ℝ := fun i => if i ∈ S then ρ i / σ i else 1
  have hu : Multipliable u := by
    apply multipliable_of_finite_mulSupport
    apply S.finite_toSet.subset
    intro i hi
    by_contra hn
    change i ∉ S at hn
    exact hi (by simp only [u, if_neg hn])
  have heq (i : ι) : (if i ∈ S then ρ i else σ i) = σ i * u i := by
    dsimp [u]
    split_ifs with hi
    · field_simp [hσ0 i]
    · simp
  have huprod : (∏' i, u i) = ∏ i ∈ S, ρ i / σ i := by
    rw [tprod_eq_prod (s := S) (fun i hi => by simp only [u, if_neg hi])]
    exact Finset.prod_congr rfl (fun i hi => by simp only [u, if_pos hi])
  rw [show (fun i => if i ∈ S then ρ i else σ i) = fun i => σ i * u i from funext heq,
    hσ.tprod_mul hu, huprod]

/-- Equality with the product of genuine restricted local densities at the
auxiliary primes and genuine ordinary densities at every other prime. -/
theorem auxiliaryCubicSingularSeries_eq_modified_product
    (p : 𝓞 K) (hp : p ≠ 0) {ν : 𝓞 K} (hν : ν ≠ 0)
    (hgood : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      p ∈ v.asIdeal → (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal)
    (σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (hσ : ∀ v, Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 (σ v)))
    (hσpos : ∀ v, 0 < σ v) (hmul : Multipliable σ) :
    let P := Ideal.span ({p} : Set (𝓞 K))
    let hP : P ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp
    auxiliaryCubicSingularSeries p hp ν =
      ((∏' v, if v ∈ idealPrimeSupport P hP then cubicModifiedResidueFactor v ν else σ v : ℝ) : ℂ) := by
  let P := Ideal.span ({p} : Set (𝓞 K))
  have hP : P ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp
  let S := idealPrimeSupport P hP
  have hden : (∏ v ∈ S, σ v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => (hσpos v).ne')
  have hformula :
      (∏' v, if v ∈ S then cubicModifiedResidueFactor v ν else σ v) * (∏ v ∈ S, σ v) =
      (∏' v, σ v) * ∏ v ∈ S, cubicModifiedResidueFactor v ν := by
    rw [finite_replacement_product_formula σ (fun v => cubicModifiedResidueFactor v ν)
      S hmul (fun v => (hσpos v).ne'), Finset.prod_div_distrib]
    field_simp [hden]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hformula
  push_cast at hc
  have hid := auxiliaryCubicSingularSeries_replacement_identity p hp ν hgood σ hσ
  change auxiliaryCubicSingularSeries p hp ν * (∏ v ∈ S, (σ v : ℂ)) =
    cubicSingularSeries ν * (∏ v ∈ S, (cubicModifiedResidueFactor v ν : ℂ)) at hid
  rw [cubicSingularSeries_eq_density_product hν σ hσ hmul] at hid
  have hdenC : (∏ v ∈ S, (σ v : ℂ)) ≠ 0 := by exact_mod_cast hden
  exact (mul_right_cancel₀ hdenC) (hid.trans hc.symm)

end WaringSiegel
#print axioms WaringSiegel.auxiliaryCubicSingularSeries_replacement_identity
#print axioms WaringSiegel.auxiliaryCubicSingularSeries_eq_modified_product
