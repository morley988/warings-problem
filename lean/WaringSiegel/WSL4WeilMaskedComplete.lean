import WaringSiegel.WSL4WeilTraceComplete
import WaringSiegel.WSL4WeilTwistInflation
import WaringSiegel.WSL4WeilCharacterMask
import WaringSiegel.WSL3IdealPoissonAuxiliary

/-! # The actual masked auxiliary Poisson coefficient, uniformly in the prime

The loss is at most 2^[K:Q], independent of the rational auxiliary prime and
of all conductor exponents.  Ramification of the auxiliary prime is allowed.
-/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical NumberField nonZeroDivisors
open NumberField Module WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def idealMaskedTwistedCubicSum (M I : Ideal (𝓞 K)) (hM : M≠0) (hMI : M≤I)
    (p : ℕ) (hMP : M≤Ideal.span ({(p:𝓞 K)} : Set (𝓞 K)))
    (ψ : AddChar (𝓞 K ⧸ I) ℂ) (χ : AddChar (𝓞 K ⧸ M) ℂ) : ℂ :=
  letI := idealResidueFintype M hM
  ∑x : 𝓞 K ⧸ M,if IsUnit (Ideal.Quotient.factor hMP x)
    then ψ (Ideal.Quotient.factor hMI (x^3))*χ x else 0

theorem idealMaskedTwistedCubicSum_kappa_bound
    (M I : Ideal (𝓞 K)) (hM : M≠0) (hI : I≠0) (hMI : M≤I)
    (p : ℕ) (hp : p.Prime) (hMP : M≤Ideal.span ({(p:𝓞 K)} : Set (𝓞 K)))
    (ψ : AddChar (𝓞 K ⧸ I) ℂ) (hψ : ψ.IsPrimitive) (χ : AddChar (𝓞 K ⧸ M) ℂ) :
    ‖idealMaskedTwistedCubicSum M I hM hMI p hMP ψ χ‖≤
      (Ideal.absNorm M:ℝ)*((2:ℝ)^finrank ℚ K*cubicKappa cubicTwistExceptionalConstant ⟨I,hI⟩) := by
  letI := idealResidueFintype M hM
  let F : (𝓞 K ⧸ M)→ℂ := fun x=>ψ (Ideal.Quotient.factor hMI (x^3))
  have hF : ∀η : AddChar (𝓞 K ⧸ M) ℂ,‖finiteLinearCharSum Finset.univ F η‖≤
      (Ideal.absNorm M:ℝ)*cubicKappa cubicTwistExceptionalConstant ⟨I,hI⟩ := by
    intro η
    exact idealTwistedCubicSum_inflated_kappa_bound M I hM hI hMI ψ hψ η
  have h := finiteLinearCharSum_coprime_prime_bound M hM p hp hMP Finset.univ F _ hF χ
  simpa only [finiteLinearCharSum,Finset.sum_filter,F,idealMaskedTwistedCubicSum,mul_left_comm] using h

theorem auxiliaryMaskedTwistedComplete_kappa_bound
    (c : CubicConductorCharacter K) (p : ℕ) (hp : p.Prime) (hp0 : (p:𝓞 K)≠0)
    (ξ : (inverseDifferent K*(auxiliaryCommonModulus c.1.1 (p:𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹)) :
    ‖auxiliaryMaskedTwistedComplete c (p:𝓞 K) hp0 (mixedEmbedding K (ξ:K))‖≤
      ((auxiliaryCommonModulus c.1.1 (p:𝓞 K)).absNorm:ℝ)*
        ((2:ℝ)^finrank ℚ K*cubicKappa cubicTwistExceptionalConstant c.1) := by
  let M := auxiliaryCommonModulus c.1.1 (p:𝓞 K)
  have hM : M≠0 := auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 (p:𝓞 K) hp0
  letI := idealResidueFintype M hM
  let χ := idealDualResidueChar M hM ξ
  have he : auxiliaryMaskedTwistedComplete c (p:𝓞 K) hp0 (mixedEmbedding K (ξ:K))=
      idealMaskedTwistedCubicSum M c.1.1 hM inf_le_left p inf_le_right c.2.1 χ := by
    unfold auxiliaryMaskedTwistedComplete idealCompleteTraceFactor idealMaskedTwistedCubicSum
    apply Finset.sum_congr rfl
    intro q _
    have hχ : archimedeanTraceCharacter (mixedEmbedding K (ξ:K))
        (mixedEmbedding K (idealResidueRepresentative M q:K))=χ q := by
      simpa only [idealResidueRepresentative_spec] using
        (idealDualResidueChar_mk M hM ξ (idealResidueRepresentative M q)).symm
    rw [hχ]
    simp only [auxiliaryMaskedResidueWeight,map_pow,ite_mul,zero_mul]
    rfl
  rw [he]
  exact idealMaskedTwistedCubicSum_kappa_bound M c.1.1 hM c.1.2 inf_le_left p hp inf_le_right
    c.2.1 ((quotient_character_primitive_iff_exact_conductor _ _).mpr c.2.2) χ
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.auxiliaryMaskedTwistedComplete_kappa_bound
