import WaringSiegel.WSL3LocalCharacterCount
import WaringSiegel.WSL2TraceMajorArcUnion

/-! # WSL3: finite quotient characters are genuine rational trace characters -/
noncomputable section
open scoped BigOperators Classical NumberField
open NumberField
namespace WaringSiegel

theorem addChar_family_surjective_of_average
    {G Q : Type*} [AddCommGroup G] [Fintype G] [Fintype Q] [Nonempty Q]
    (χ : Q → AddChar G ℂ)
    (havg : ∀ x : G, (𝔼 q : Q, χ q x) = if x = 0 then 1 else 0) :
    Function.Surjective χ := by
  have hN : (Fintype.card Q : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum (x : G) : (∑ q : Q, χ q x) =
      if x = 0 then (Fintype.card Q : ℂ) else 0 := by
    have h := havg x
    rw [Fintype.expect_eq_sum_div_card] at h
    have he := (div_eq_iff hN).mp h
    simpa only [ite_mul, one_mul, zero_mul] using he
  intro ψ
  by_contra hnone
  have hne (q : Q) : χ q ≠ ψ := fun h => hnone ⟨q, h⟩
  have hinner (q : Q) : (∑ x : G, χ q x * (ψ x)⁻¹) = 0 := by
    have hn : χ q - ψ ≠ 0 := sub_ne_zero.mpr (hne q)
    simpa only [AddChar.sub_apply', div_eq_mul_inv] using
      (AddChar.sum_eq_zero_iff_ne_zero.mpr hn)
  have hzero : (∑ x : G, ∑ q : Q, χ q x * (ψ x)⁻¹) = 0 := by
    rw [Finset.sum_comm]
    simp only [hinner, Finset.sum_const_zero]
  have hnonzero : (∑ x : G, ∑ q : Q, χ q x * (ψ x)⁻¹) = (Fintype.card Q : ℂ) := by
    simp only [← Finset.sum_mul, hsum, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ψ.map_zero_eq_one, inv_one, mul_one]
  exact hN (hnonzero.symm.trans hzero)

variable {K : Type*} [Field K] [NumberField K]

/-- Every additive character of the principal residue ring is induced by
an actual rational center in the trace torus. -/
theorem traceResidueAddChar_surjective (a : 𝓞 K) (ha : a ≠ 0)
    [Fintype (traceTorusMul a).ker] :
    Function.Surjective (traceResidueAddChar a) := by
  letI := principalResidueRing_finite a ha
  letI := Fintype.ofFinite (PrincipalResidueRing a)
  exact addChar_family_surjective_of_average (traceResidueAddChar a)
    (traceResidueAddChar_average a ha)

/-- Literal field representatives exist for every principal-quotient character. -/
theorem principal_character_has_rational_trace_representative
    (a : 𝓞 K) (ha : a ≠ 0) (ψ : AddChar (PrincipalResidueRing a) ℂ) :
    ∃ γ : K, (a : K) * γ ∈ inverseDifferent K ∧
      ∀ x : 𝓞 K, ψ (Ideal.Quotient.mk (Ideal.span {a}) x) =
        traceTorusCharacter x (traceRationalPoint γ) := by
  letI := traceTorusMul_kernel_finite_type a ha
  letI := Fintype.ofFinite (traceTorusMul a).ker
  obtain ⟨q, hq⟩ := traceResidueAddChar_surjective a ha ψ
  obtain ⟨γ, hγ, hpoint⟩ := traceTorusMul_kernel_representative a ha q.property
  refine ⟨γ, (traceKernelFractionalIdeal_mem a ha γ).mp hγ, ?_⟩
  intro x
  rw [← hq, traceResidueAddChar_mk]
  change traceTorusCharacter x q = traceTorusCharacter x (Submodule.Quotient.mk _)
  rw [hpoint]

end WaringSiegel

#print axioms WaringSiegel.principal_character_has_rational_trace_representative
