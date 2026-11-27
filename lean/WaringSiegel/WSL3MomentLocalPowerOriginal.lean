import WaringSiegel.WSL3MomentLocalPowerAllProducts
import WaringSiegel.WSL2LocalPrimePowerQuotient

/-!
# Original prime-power power counts and exact complete-character formulas

The all-prime lower bounds are transported from completed integer rings
to the original quotients O_K / p^e. The normalized counts are exactly
the complete-character sums used by the singular-series calculation.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing Filter Topology
open scoped NumberField BigOperators
namespace WaringSiegel.WSL3

theorem localPowerSolutionCount_congr
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (k p : ℕ) (a : R) (b : S)
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (hab : e (Ideal.Quotient.mk I a)=Ideal.Quotient.mk J b) :
    localPowerSolutionCount R I k p a=localPowerSolutionCount S J k p b := by
  unfold localPowerSolutionCount
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨fun i => e (x.val i),by
        change (∑ i,e (x.val i)^k)=_
        simpa only [map_sum,map_pow] using (congrArg e x.property).trans hab⟩
      invFun := fun y => ⟨fun i => e.symm (y.val i),by
        apply e.injective
        rw [map_sum]
        simp only [map_pow,e.apply_symm_apply]
        exact y.property.trans hab.symm⟩
      left_inv := fun x => by apply Subtype.ext; funext i; exact e.symm_apply_apply _
      right_inv := fun y => by apply Subtype.ext; funext i; exact e.apply_symm_apply _ }

variable {K : Type*} [Field K] [NumberField K]

theorem primePower_power_solution_count_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k p e : ℕ) (target : 𝓞 K) :
    localPowerSolutionCount (𝓞 K) (v.asIdeal^e) k p target=
      localPowerSolutionCount (v.adicCompletionIntegers K)
        (maximalIdeal (v.adicCompletionIntegers K)^e) k p
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  apply localPowerSolutionCount_congr _ _ _ _ _ _ (primePowerCompletionEquiv v e)
  rfl

def normalizedPrimePowerCount
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k p e : ℕ) (target : 𝓞 K) : ℝ :=
  (localPowerSolutionCount (𝓞 K) (v.asIdeal^e) k p target:ℝ)/
    (Ideal.absNorm v.asIdeal:ℝ)^((p-1)*e)

theorem normalizedPrimePowerCount_eq_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k p e : ℕ) (target : 𝓞 K) :
    normalizedPrimePowerCount v k p e target=
      normalizedLocalPowerCount (v.adicCompletionIntegers K) k p e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) target) := by
  unfold normalizedPrimePowerCount normalizedLocalPowerCount
  rw [primePower_power_solution_count_eq,completion_residue_card_eq_absNorm]

theorem primePower_power_normalized_character_formula
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k p e : ℕ) (hp : 1≤p) (target : 𝓞 K)
    [Fintype (𝓞 K ⧸ v.asIdeal^e)] :
    (normalizedPrimePowerCount v k p e target:ℂ)=
      ∑ ψ : AddChar (𝓞 K ⧸ v.asIdeal^e) ℂ,
        (finiteRingPowerSum ψ k/(Ideal.absNorm (v.asIdeal^e):ℂ))^p *
          ψ (-Ideal.Quotient.mk (v.asIdeal^e) target) := by
  have hc : Fintype.card (𝓞 K ⧸ v.asIdeal^e)=Ideal.absNorm (v.asIdeal^e) := by
    rw [← Nat.card_eq_fintype_card,Ideal.absNorm_apply]
    rfl
  rw [← hc,finite_ring_power_normalized_character_count k p hp]
  unfold normalizedPrimePowerCount localPowerSolutionCount LocalPowerSolutions
  push_cast
  rw [hc,map_pow,Nat.cast_pow,← pow_mul,Nat.mul_comm e (p-1)]

theorem original_power_count_finite_products_uniform_positive
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) :
    ∃ c : ℝ,0<c ∧ ∀ target : 𝓞 K,LocalUnitSolvable k p target →
      ∀ e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ,
        (∀ v,powerLocalPrecision (v.adicCompletionIntegers K) k≤e v) →
      ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        c≤∏ v∈S,normalizedPrimePowerCount v k p (e v) target := by
  simpa only [normalizedPrimePowerCount_eq_completion] using
    completion_power_count_all_finite_products_uniform_positive (K := K) k p hk hp

#print axioms primePower_power_solution_count_eq
#print axioms primePower_power_normalized_character_formula
#print axioms original_power_count_finite_products_uniform_positive
end WaringSiegel.WSL3
