import WaringSiegel.WSL4WeilIdealCRT

/-! # Arbitrary linear twists after modulus inflation

A twist which descends has the same normalized average.  A twist which does
not descend cancels exactly under translation in the reduction kernel.
-/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical NumberField

theorem twistedPowerSum_average_inflation
    {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
    (f : A→+*B) (hf : Function.Surjective f) (ψ χ : AddChar B ℂ) (k : ℕ) :
    twistedPowerSum (ψ.compAddMonoidHom f.toAddMonoidHom)
      (χ.compAddMonoidHom f.toAddMonoidHom) k/(Fintype.card A:ℂ)=
      twistedPowerSum ψ χ k/(Fintype.card B:ℂ) := by
  change (∑x : A,ψ (f (x^k))*χ (f x))/(Fintype.card A:ℂ)=
    (∑x : B,ψ (x^k)*χ x)/(Fintype.card B:ℂ)
  simp only [map_pow]
  exact finite_average_surjective_addHom f.toAddMonoidHom hf (fun x=>ψ (x^k)*χ x)

theorem twistedPowerSum_inflated_eq_zero
    {A B : Type*} [CommRing A] [CommRing B] [Fintype A]
    (f : A→+*B) (ψ : AddChar B ℂ) (χ : AddChar A ℂ) (k : ℕ)
    (t : A) (ht : f t=0) (hχ : χ t≠1) :
    twistedPowerSum (ψ.compAddMonoidHom f.toAddMonoidHom) χ k=0 := by
  let S := twistedPowerSum (ψ.compAddMonoidHom f.toAddMonoidHom) χ k
  have hshift : S=S*χ t := by
    have h := (Equiv.addRight t).bijective.sum_comp (fun x : A=>ψ ((f x)^k)*χ x)
    change (∑x : A,ψ ((f (x+t))^k)*χ (x+t))=(∑x : A,ψ ((f x)^k)*χ x) at h
    simp only [map_add,ht,add_zero,χ.map_add_eq_mul,← mul_assoc,← Finset.sum_mul] at h
    change (∑x : A,ψ (f (x^k))*χ x)=(∑x : A,ψ (f (x^k))*χ x)*χ t
    simpa only [map_pow] using h.symm
  by_contra hS
  apply hχ
  apply mul_left_cancel₀ hS
  simpa only [mul_one] using hshift.symm

variable {K : Type*} [Field K] [NumberField K]

theorem idealTwistedCubicSum_inflated_kappa_bound
    (M I : Ideal (𝓞 K)) (hM : M≠0) (hI : I≠0) (hMI : M≤I)
    (ψ : AddChar (𝓞 K ⧸ I) ℂ) (hψ : ψ.IsPrimitive)
    (χ : AddChar (𝓞 K ⧸ M) ℂ) :
    ‖idealTwistedCubicSum M hM
      (ψ.compAddMonoidHom (Ideal.Quotient.factor hMI).toAddMonoidHom) χ‖≤
        (Ideal.absNorm M:ℝ)*cubicKappa cubicTwistExceptionalConstant ⟨I,hI⟩ := by
  letI := idealResidueFintype M hM
  letI := idealResidueFintype I hI
  let f := Ideal.Quotient.factor hMI
  by_cases hC : I≤quotientCharacterConductor M χ
  · obtain ⟨η,rfl⟩ := (quotient_character_factors_iff hMI χ).mpr hC
    have havg := twistedPowerSum_average_inflation f (Ideal.Quotient.factor_surjective hMI) ψ η 3
    have hcardM : Fintype.card (𝓞 K ⧸ M)=Ideal.absNorm M := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    have hcardI : Fintype.card (𝓞 K ⧸ I)=Ideal.absNorm I := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    have hnorm := congrArg norm havg
    simp only [norm_div,Complex.norm_natCast,hcardM,hcardI] at hnorm
    have hposM : 0<(Ideal.absNorm M:ℝ) := by
      rw [← hcardM]; exact_mod_cast Fintype.card_pos
    have hposI : 0<(Ideal.absNorm I:ℝ) := by
      rw [← hcardI]; exact_mod_cast Fintype.card_pos
    have hb := idealTwistedCubicSum_kappa_bound I hI ψ η hψ
    have hdiv : ‖twistedPowerSum (ψ.compAddMonoidHom f.toAddMonoidHom)
        (η.compAddMonoidHom f.toAddMonoidHom) 3‖/(Ideal.absNorm M:ℝ)≤
          cubicKappa cubicTwistExceptionalConstant ⟨I,hI⟩ := by
      rw [hnorm]
      exact (div_le_iff₀ hposI).mpr (by simpa only [mul_comm,idealTwistedCubicSum] using hb)
    simpa only [mul_comm,idealTwistedCubicSum,f] using (div_le_iff₀ hposM).mp hdiv
  · have hz : idealTwistedCubicSum M hM (ψ.compAddMonoidHom f.toAddMonoidHom) χ=0 := by
      by_contra hsum
      apply hC
      intro a ha b
      change χ (Ideal.Quotient.mk M (a*b))=1
      by_contra hchar
      have ht : f (Ideal.Quotient.mk M (a*b))=0 := by
        rw [Ideal.Quotient.factor_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right b ha)
      exact hsum (twistedPowerSum_inflated_eq_zero f ψ χ 3 _ ht hchar)
    rw [show (Ideal.Quotient.factor hMI)=f from rfl,hz,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (cubicKappa_nonneg _ cubicTwistExceptionalConstant_nonneg _)
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.idealTwistedCubicSum_inflated_kappa_bound
