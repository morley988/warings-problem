import WaringSiegel.WSL3AuxiliaryEulerFinite
import Mathlib.Order.Filter.AtTopBot.Prod

/-! # Cofinal literal quotient sums for the auxiliary and ordinary series -/
noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def conductorCharacterFinset (M : Ideal (𝓞 K)) (hM : M ≠ 0) :
    Finset (CubicConductorCharacter K) :=
  letI := conductorCharactersUnderFintype M hM
  (Finset.univ : Finset (ConductorCharactersUnder M)).map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_conductorCharacterFinset (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (c : CubicConductorCharacter K) : c ∈ conductorCharacterFinset M hM ↔ M ≤ c.1.1 := by
  letI := conductorCharactersUnderFintype M hM
  simp only [conductorCharacterFinset, Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨fun ⟨d,hd⟩ => hd ▸ d.2, fun h => ⟨⟨c,h⟩,rfl⟩⟩

theorem auxiliaryCubicCharacterContribution_finite_sum
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (hMP : M ≤ Ideal.span ({p} : Set (𝓞 K))) :
    (∑ c ∈ conductorCharacterFinset M hM, auxiliaryCubicCharacterContribution c p hp ν) =
      idealMaskedCubicSum M hM (Ideal.span ({p} : Set (𝓞 K))) hMP p ν := by
  letI := idealResidueFintype M hM
  letI := conductorCharactersUnderFintype M hM
  let f := fun ψ : AddChar (𝓞 K ⧸ M) ℂ =>
    finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hMP)
      (Ideal.Quotient.mk M p) (Ideal.Quotient.mk M ν) ψ
  have he (c : ConductorCharactersUnder M) :
      f ((conductorCharactersUnderEquiv M hM) c) = auxiliaryCubicCharacterContribution c.1 p hp ν := by
    exact (auxiliaryCubicCharacterContribution_common_multiple c.1 p hp ν M hM c.2 hMP).symm
  have hs := (conductorCharactersUnderEquiv M hM).bijective.sum_comp f
  simpa only [conductorCharacterFinset, Finset.sum_map, Function.Embedding.coeFn_mk,
    he, f, idealMaskedCubicSum] using hs

theorem cubicCharacterContribution_finite_sum
    (ν : 𝓞 K) (M : Ideal (𝓞 K)) (hM : M ≠ 0) :
    (∑ c ∈ conductorCharacterFinset M hM, cubicCharacterContribution c ν) =
      idealOrdinaryCubicSum M hM ν := by
  letI := idealResidueFintype M hM
  letI := conductorCharactersUnderFintype M hM
  let f := fun ψ : AddChar (𝓞 K ⧸ M) ℂ =>
    finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk M ν) ψ
  have he (c : ConductorCharactersUnder M) :
      f ((conductorCharactersUnderEquiv M hM) c) = cubicCharacterContribution c.1 ν := by
    letI := idealResidueFintype c.1.1.1 c.1.1.2
    change finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk M ν)
      (c.1.2.1.compAddMonoidHom (Ideal.Quotient.factor c.2).toAddMonoidHom) = _
    rw [finite_ring_power_character_term_inflation (Ideal.Quotient.factor c.2)
      (Ideal.Quotient.factor_surjective c.2)]
    rfl
  have hs := (conductorCharactersUnderEquiv M hM).bijective.sum_comp f
  simpa only [conductorCharacterFinset, Finset.sum_map, Function.Embedding.coeFn_mk,
    he, f, idealOrdinaryCubicSum] using hs

abbrev AuxiliaryEulerIndex (K : Type*) [Field K] [NumberField K] :=
  Finset (CubicConductorCharacter K) × ℕ

def auxiliaryEulerModulus (p : 𝓞 K) (z : AuxiliaryEulerIndex K) : Ideal (𝓞 K) :=
  (Ideal.span ({p} : Set (𝓞 K)))^(z.2+1) * ∏ c ∈ z.1, c.1.1

theorem auxiliaryEulerModulus_ne_zero (p : 𝓞 K) (hp : p ≠ 0) (z : AuxiliaryEulerIndex K) :
    auxiliaryEulerModulus p z ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (mt Ideal.span_singleton_eq_bot.mp hp))
    (Finset.prod_ne_zero_iff.mpr (fun c _ => c.1.2))

theorem auxiliaryEulerModulus_le_mask (p : 𝓞 K) (z : AuxiliaryEulerIndex K) :
    auxiliaryEulerModulus p z ≤ Ideal.span ({p} : Set (𝓞 K)) :=
  Ideal.mul_le_right.trans (Ideal.pow_le_self (Nat.succ_ne_zero _))

theorem auxiliaryEulerModulus_le_conductor (p : 𝓞 K) (z : AuxiliaryEulerIndex K)
    (c : CubicConductorCharacter K) (hc : c ∈ z.1) :
    auxiliaryEulerModulus p z ≤ c.1.1 :=
  Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hc))

theorem auxiliaryEulerModulus_cofinal (p : 𝓞 K) (hp : p ≠ 0) :
    Tendsto (fun z : AuxiliaryEulerIndex K =>
      conductorCharacterFinset (auxiliaryEulerModulus p z) (auxiliaryEulerModulus_ne_zero p hp z))
      atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [eventually_ge_atTop (S,0)] with z hz
  intro c hc
  exact (mem_conductorCharacterFinset _ _ c).mpr
    (auxiliaryEulerModulus_le_conductor p z c (hz.1 hc))

theorem auxiliaryEulerModulus_prime_exponent_lower (p : 𝓞 K) (hp : p ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hpv : p ∈ v.asIdeal)
    (z : AuxiliaryEulerIndex K) :
    z.2+1 ≤ idealPrimeExponent (auxiliaryEulerModulus p z) v := by
  have hPv : Ideal.span ({p} : Set (𝓞 K)) ≤ v.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpv
  have hMv : auxiliaryEulerModulus p z ≤ v.asIdeal^(z.2+1) :=
    Ideal.mul_le_right.trans (pow_le_pow_left' hPv _)
  have he := idealPrimeExponent_mono_of_le _ _
    (auxiliaryEulerModulus_ne_zero p hp z) (pow_ne_zero _ v.ne_bot) hMv v
  simpa only [idealPrimeExponent_prime_pow, if_pos rfl] using he

theorem auxiliaryEulerModulus_prime_exponent_tendsto (p : 𝓞 K) (hp : p ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hpv : p ∈ v.asIdeal) :
    Tendsto (fun z : AuxiliaryEulerIndex K => idealPrimeExponent (auxiliaryEulerModulus p z) v)
      atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (∅,n)] with z hz
  exact hz.2.trans (Nat.le_succ _ |>.trans (auxiliaryEulerModulus_prime_exponent_lower p hp v hpv z))

theorem idealMaskedCubicSum_tendsto (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (hs : Summable (fun c : CubicConductorCharacter K => auxiliaryCubicCharacterContribution c p hp ν)) :
    Tendsto (fun z : AuxiliaryEulerIndex K => idealMaskedCubicSum (auxiliaryEulerModulus p z)
      (auxiliaryEulerModulus_ne_zero p hp z) (Ideal.span ({p} : Set (𝓞 K)))
      (auxiliaryEulerModulus_le_mask p z) p ν) atTop (𝓝 (auxiliaryCubicSingularSeries p hp ν)) := by
  have ht := hs.hasSum.comp (auxiliaryEulerModulus_cofinal p hp)
  have heq (z : AuxiliaryEulerIndex K) := auxiliaryCubicCharacterContribution_finite_sum
    p hp ν (auxiliaryEulerModulus p z) (auxiliaryEulerModulus_ne_zero p hp z)
    (auxiliaryEulerModulus_le_mask p z)
  simpa only [Function.comp_def, heq, auxiliaryCubicSingularSeries] using ht

theorem idealOrdinaryCubicSum_tendsto (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    Tendsto (fun z : AuxiliaryEulerIndex K => idealOrdinaryCubicSum (auxiliaryEulerModulus p z)
      (auxiliaryEulerModulus_ne_zero p hp z) ν) atTop (𝓝 (cubicSingularSeries ν)) := by
  have ht := (cubicCharacterContribution_norm_summable ν).of_norm.hasSum.comp
    (auxiliaryEulerModulus_cofinal p hp)
  simpa only [Function.comp_def, cubicCharacterContribution_finite_sum, cubicCharacterContribution_tsum] using ht

end WaringSiegel
#print axioms WaringSiegel.idealMaskedCubicSum_tendsto
#print axioms WaringSiegel.idealOrdinaryCubicSum_tendsto
