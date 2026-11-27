import WaringSiegel.WSL4WeilPrimePowers

/-! # Coprime factorization and the global literal twisted cubic bound -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical NumberField
variable {K : Type*} [Field K] [NumberField K]

def idealTwistedCubicSum (I : Ideal (𝓞 K)) (hI : I≠0)
    (ψ χ : AddChar (𝓞 K ⧸ I) ℂ) : ℂ :=
  letI := idealResidueFintype I hI
  twistedPowerSum ψ χ 3

theorem idealTwistedCubicSum_coprime_bound
    (I J : Ideal (𝓞 K)) (hI : I≠0) (hJ : J≠0) (h : IsCoprime I J)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hbI : ∀ψ χ : AddChar (𝓞 K ⧸ I) ℂ, ψ.IsPrimitive →
      ‖idealTwistedCubicSum I hI ψ χ‖≤(Ideal.absNorm I : ℝ)*B)
    (hbJ : ∀ψ χ : AddChar (𝓞 K ⧸ J) ℂ, ψ.IsPrimitive →
      ‖idealTwistedCubicSum J hJ ψ χ‖≤(Ideal.absNorm J : ℝ)*C)
    (ψ χ : AddChar (𝓞 K ⧸ I*J) ℂ) (hψ : ψ.IsPrimitive) :
    ‖idealTwistedCubicSum (I*J) (mul_ne_zero hI hJ) ψ χ‖≤
      (Ideal.absNorm (I*J) : ℝ)*(B*C) := by
  letI := idealResidueFintype I hI
  letI := idealResidueFintype J hJ
  letI := idealResidueFintype (I*J) (mul_ne_zero hI hJ)
  obtain ⟨⟨ψ₁,ψ₂⟩,rfl⟩ := (crtAddCharEquiv I J h).surjective ψ
  obtain ⟨⟨χ₁,χ₂⟩,rfl⟩ := (crtAddCharEquiv I J h).surjective χ
  have hp := (quotientCharacterConductor_crt_exact_iff I J h ψ₁ ψ₂).mp
    ((quotient_character_primitive_iff_exact_conductor _ _).mp hψ)
  have hp₁ := (quotient_character_primitive_iff_exact_conductor _ _).mpr hp.1
  have hp₂ := (quotient_character_primitive_iff_exact_conductor _ _).mpr hp.2
  change ‖twistedPowerSum _ _ 3‖≤_
  rw [twistedPowerSum_crt,norm_mul]
  calc
    _ ≤ ((Ideal.absNorm I : ℝ)*B)*((Ideal.absNorm J : ℝ)*C) :=
      mul_le_mul (hbI ψ₁ χ₁ hp₁) (hbJ ψ₂ χ₂ hp₂) (norm_nonneg _) (by positivity)
    _ = _ := by rw [map_mul]; push_cast; ring

theorem idealTwistedCubicSum_one
    (ψ χ : AddChar (𝓞 K ⧸ (1 : Ideal (𝓞 K))) ℂ) :
    idealTwistedCubicSum 1 one_ne_zero ψ χ=1 := by
  letI := idealResidueFintype (1 : Ideal (𝓞 K)) one_ne_zero
  letI : Subsingleton (𝓞 K ⧸ (1 : Ideal (𝓞 K))) := by
    rw [Ideal.one_eq_top]
    infer_instance
  letI : Unique (𝓞 K ⧸ (1 : Ideal (𝓞 K))) :=
    { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  simp [idealTwistedCubicSum,twistedPowerSum, show (default : 𝓞 K ⧸ (1 : Ideal (𝓞 K)))=0 from rfl]

theorem idealTwistedCubicSum_finset_prime_power_bound
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ) :
    ∀ (hN : (∏v∈S,v.asIdeal^(e v+1))≠0) (ψ χ : AddChar (𝓞 K ⧸ (∏v∈S,v.asIdeal^(e v+1))) ℂ), ψ.IsPrimitive →
      ‖idealTwistedCubicSum _ hN ψ χ‖≤
        (Ideal.absNorm (∏v∈S,v.asIdeal^(e v+1)) : ℝ)*
          ∏v∈S,cubicKappaLocal (Ideal.absNorm v.asIdeal) (cubicTwistExceptionalConstant v)
            (cubicKappaGood v) (e v) := by
  induction S using Finset.induction_on with
  | empty =>
    intro hN ψ χ hψ
    simpa only [Finset.prod_empty,idealTwistedCubicSum_one,norm_one,map_one,
      Nat.cast_one,one_mul] using (le_refl (1:ℝ))
  | @insert v S hv ih =>
    have hcop : IsCoprime (v.asIdeal^(e v+1)) (∏w∈S,w.asIdeal^(e w+1)) := by
      apply IsCoprime.prod_right
      intro w hw
      exact heightOne_prime_powers_coprime v w (fun he=>hv (he ▸ hw)) _ _
    rw [Finset.prod_insert hv]
    simp only [Finset.prod_insert hv]
    intro hN ψ χ hψ
    apply idealTwistedCubicSum_coprime_bound _ _ (pow_ne_zero _ v.ne_bot)
      (prime_power_product_ne_zero S (fun w=>e w+1)) hcop
      (cubicKappaLocal (Ideal.absNorm v.asIdeal) (cubicTwistExceptionalConstant v) (cubicKappaGood v) (e v)) _
      (cubicKappaLocal_nonneg _ _ _ _ (Nat.cast_nonneg _) (cubicTwistExceptionalConstant_nonneg v))
      (Finset.prod_nonneg (fun w _=>cubicKappaLocal_nonneg _ _ _ _ (Nat.cast_nonneg _)
        (cubicTwistExceptionalConstant_nonneg w))) _ (ih (prime_power_product_ne_zero S (fun w=>e w+1))) ψ χ hψ
    intro φ η hφ
    letI := idealResidueFintype (v.asIdeal^(e v+1)) (pow_ne_zero _ v.ne_bot)
    simpa only [idealTwistedCubicSum,map_pow,Nat.cast_pow] using
      twistedCubicSum_prime_power_bound v (e v) φ η hφ

theorem idealTwistedCubicSum_kappa_bound
    (I : Ideal (𝓞 K)) (hI : I≠0) (ψ χ : AddChar (𝓞 K ⧸ I) ℂ) (hψ : ψ.IsPrimitive) :
    ‖idealTwistedCubicSum I hI ψ χ‖≤(Ideal.absNorm I : ℝ)*
      cubicKappa cubicTwistExceptionalConstant ⟨I,hI⟩ := by
  let S := idealPrimeSupport I hI
  let e := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)=>idealPrimeExponent I v-1
  have he : (∏v∈S,v.asIdeal^(e v+1))=I := by
    calc
      _ = ∏v∈S,v.asIdeal^idealPrimeExponent I v := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [show e v+1=idealPrimeExponent I v from Nat.sub_add_cancel (idealPrimeExponent_pos_of_mem I hI v hv)]
      _ = I := idealPrimeSupport_factorization I hI
  have hk : cubicKappa cubicTwistExceptionalConstant ⟨I,hI⟩=
      ∏v∈S,cubicKappaLocal (Ideal.absNorm v.asIdeal) (cubicTwistExceptionalConstant v)
        (cubicKappaGood v) (e v) := by
    unfold cubicKappa nonzeroIdealConductorGraph
    rw [Finset.prod_image (fun _ _ _ _ h=>congrArg Prod.fst h)]
  have h := idealTwistedCubicSum_finset_prime_power_bound S e
  rw [he] at h
  rw [hk]
  exact h hI ψ χ hψ
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.idealTwistedCubicSum_kappa_bound
