import WaringSiegel.WSL3AuxiliaryFiniteIndex

/-! # WSL3: the literal auxiliary character series is controlled by finite quotient masses -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

/-- Every finite family of exact conductor characters embeds in a common
nonzero quotient that also carries the auxiliary unit restriction. -/
theorem finite_conductors_common_multiple
    (p : 𝓞 K) (hp : p ≠ 0) (S : Finset (CubicConductorCharacter K)) :
    ∃ M : Ideal (𝓞 K), M ≠ 0 ∧ M ≤ Ideal.span ({p} : Set (𝓞 K)) ∧
      ∀ c ∈ S, M ≤ c.1.1 := by
  let P := Ideal.span ({p} : Set (𝓞 K))
  have hP : P ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp
  refine ⟨P * ∏ c ∈ S, c.1.1, ?_, Ideal.mul_le_right, ?_⟩
  · exact mul_ne_zero hP (Finset.prod_ne_zero_iff.mpr (fun c _ => c.1.2))
  · intro c hc
    exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hc))

/-- This is a finite-to-infinite passage for the actual complete-sum terms.
The sole premise is the explicit uniform finite quotient mass inequality. -/
theorem auxiliary_weighted_summable_of_finite_mass_bound
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) (t C : ℝ)
    (hfinite : ∀ (M : Ideal (𝓞 K)) (hM : M ≠ 0)
      (hMP : M ≤ Ideal.span ({p} : Set (𝓞 K))),
      letI := idealResidueFintype M hM
      finiteMaskedConductorMass M (Ideal.span ({p} : Set (𝓞 K))) hMP p ν t ≤ C) :
    Summable (fun c : CubicConductorCharacter K =>
      (Ideal.absNorm c.1.1 : ℝ)^t * ‖auxiliaryCubicCharacterContribution c p hp ν‖) ∧
    (∑' c : CubicConductorCharacter K,
      (Ideal.absNorm c.1.1 : ℝ)^t * ‖auxiliaryCubicCharacterContribution c p hp ν‖) ≤ C := by
  let w := fun c : CubicConductorCharacter K =>
    (Ideal.absNorm c.1.1 : ℝ)^t * ‖auxiliaryCubicCharacterContribution c p hp ν‖
  have hw (c : CubicConductorCharacter K) : 0 ≤ w c := by dsimp [w]; positivity
  have hb (S : Finset (CubicConductorCharacter K)) : ∑ c ∈ S, w c ≤ C := by
    obtain ⟨M,hM,hMP,hS⟩ := finite_conductors_common_multiple p hp S
    letI := idealResidueFintype M hM
    letI := conductorCharactersUnderFintype M hM
    let f : S → ConductorCharactersUnder M := fun c => ⟨c.1,hS c.1 c.2⟩
    have hf : Function.Injective f := by
      intro c d h
      apply Subtype.ext
      exact congrArg (fun x : ConductorCharactersUnder M => x.1) h
    have hsub := Summable.tsum_le_tsum_of_inj f hf
      (fun c _ => hw c.1) (fun c => le_rfl)
      (show Summable (fun c : S => w c.1) from Summable.of_finite)
      (show Summable (fun c : ConductorCharactersUnder M => w c.1) from Summable.of_finite)
    have hsub' : (∑ c ∈ S, w c) ≤ ∑ c : ConductorCharactersUnder M, w c.1 := by
      simpa only [tsum_fintype, f, Finset.sum_coe_sort] using hsub
    have he := auxiliaryCubicCharacterContribution_finite_mass p hp ν M hM hMP t
    change (∑ c : ConductorCharactersUnder M, w c.1) =
      finiteMaskedConductorMass M (Ideal.span ({p} : Set (𝓞 K))) hMP p ν t at he
    exact hsub'.trans (he.trans_le (hfinite M hM hMP))
  have hs : Summable w := summable_of_sum_le hw hb
  exact ⟨hs,hs.tsum_le_of_sum_le hb⟩

end WaringSiegel
#print axioms WaringSiegel.auxiliary_weighted_summable_of_finite_mass_bound
