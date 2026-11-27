import WaringSiegel.WSL4PowerIdealSeries

/-! # Exact finite Euler factorization of the actual degree-k ideal coefficients -/
noncomputable section
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {K:Type*} [Field K] [NumberField K]

@[simp] theorem idealPrimitivePowerCoefficient_prime_pow
    (k p:ℕ) (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e:ℕ) (ν:𝓞 K) :
    idealPrimitivePowerCoefficient k p (v.asIdeal^e) (pow_ne_zero e v.ne_bot) ν=
      primePowerPrimitivePowerCoefficient k p v e ν := rfl

@[simp] theorem idealPrimitivePowerCoefficient_top (k p:ℕ) (hp:1≤p) (ν:𝓞 K) :
    idealPrimitivePowerCoefficient k p ⊤ top_ne_bot ν=1 := by
  letI := idealResidueFintype (⊤:Ideal (𝓞 K)) top_ne_bot
  letI : Unique (𝓞 K⧸(⊤:Ideal (𝓞 K))) :=
    { default := 0
      uniq := fun _ => Subsingleton.elim _ _ }
  have hC (ψ:AddChar (𝓞 K⧸(⊤:Ideal (𝓞 K))) ℂ) : quotientCharacterConductor ⊤ ψ=⊤ := by
    apply top_unique
    exact ideal_le_quotientCharacterConductor ⊤ ψ
  simp only [idealPrimitivePowerCoefficient,primitiveConductorCharacters,hC,Finset.filter_true,
    finiteRingPowerCharacterTerm]
  rw [finite_ring_power_normalized_character_count k p hp]
  change (localPowerSolutionCount (𝓞 K) ⊤ k p ν:ℂ)/(Fintype.card (𝓞 K⧸(⊤:Ideal (𝓞 K))):ℂ)^(p-1)=1
  simp only [localPowerSolutionCount_top,Fintype.card_unique,Nat.cast_one,one_pow,div_one]

@[simp] theorem idealPrimitivePowerCoefficient_one (k p:ℕ) (hp:1≤p) (ν:𝓞 K) :
    idealPrimitivePowerCoefficient k p 1 one_ne_zero ν=1 := by
  simpa only [Ideal.one_eq_top] using idealPrimitivePowerCoefficient_top k p hp ν

theorem idealPrimitivePowerCoefficient_finset_prod (k p:ℕ) (hp:1≤p)
    (S:Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (e:IsDedekindDomain.HeightOneSpectrum (𝓞 K)→ℕ) (ν:𝓞 K) :
    idealPrimitivePowerCoefficient k p (∏ v∈S,v.asIdeal^e v) (prime_power_product_ne_zero S e) ν=
      ∏ v∈S,primePowerPrimitivePowerCoefficient k p v (e v) ν := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using idealPrimitivePowerCoefficient_one k p hp ν
  | @insert v S hv ih =>
    have hcop:IsCoprime (v.asIdeal^e v) (∏ w∈S,w.asIdeal^e w) := by
      apply IsCoprime.prod_right
      intro w hw
      exact heightOne_prime_powers_coprime v w (fun he => hv (he ▸ hw)) _ _
    simp only [Finset.prod_insert hv]
    rw [idealPrimitivePowerCoefficient_mul _ _ _ _ (pow_ne_zero _ v.ne_bot)
      (prime_power_product_ne_zero S e) hcop,idealPrimitivePowerCoefficient_prime_pow,ih]

theorem idealPrimitivePowerCoefficient_eq_graph_product (k p:ℕ) (hp:1≤p)
    (I:{I:Ideal (𝓞 K)//I≠0}) (ν:𝓞 K) :
    idealPrimitivePowerCoefficient k p I.1 I.2 ν=
      ∏ ve∈nonzeroIdealConductorGraph I,primePowerPrimitivePowerCoefficient k p ve.1 (ve.2+1) ν := by
  have h := idealPrimitivePowerCoefficient_finset_prod k p hp
    (idealPrimeSupport I.1 I.2) (idealPrimeExponent I.1) ν
  simp only [idealPrimeSupport_factorization] at h
  rw [h]
  unfold nonzeroIdealConductorGraph
  rw [Finset.prod_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  apply Finset.prod_congr rfl
  intro v hv
  rw [Nat.sub_add_cancel (idealPrimeExponent_pos_of_mem I.1 I.2 v hv)]

#print axioms idealPrimitivePowerCoefficient_finset_prod
#print axioms idealPrimitivePowerCoefficient_eq_graph_product
end WaringSiegel.WSL4Local
