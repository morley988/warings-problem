import WaringSiegel.WSL3ConductorCRTCharacters

/-! # WSL3: exact conductors are multiplicative under coprime CRT -/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel

theorem quotientCharacterConductor_crt {R : Type*} [CommRing R]
    (I J : Ideal R) (h : IsCoprime I J)
    (ψ : AddChar (R ⧸ I) ℂ) (φ : AddChar (R ⧸ J) ℂ) :
    quotientCharacterConductor (I*J) (crtAddCharEquiv I J h (ψ,φ)) =
      quotientCharacterConductor I ψ ⊓ quotientCharacterConductor J φ := by
  have hsep (y : R ⧸ I) (z : R ⧸ J) :
      ∃ x : R, Ideal.Quotient.mk I x = y ∧ Ideal.Quotient.mk J x = z := by
    obtain ⟨q, hq⟩ := (Ideal.quotientMulEquivQuotientProd I J h).surjective (y,z)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨x, congrArg Prod.fst hq, congrArg Prod.snd hq⟩
  ext a
  constructor
  · intro ha
    constructor
    · intro b
      obtain ⟨x, hxI, hxJ⟩ := hsep (Ideal.Quotient.mk I b) 0
      have hh := ha x
      change ψ (Ideal.Quotient.mk I (a*x)) * φ (Ideal.Quotient.mk J (a*x)) = 1 at hh
      rw [(Ideal.Quotient.mk I).map_mul, (Ideal.Quotient.mk J).map_mul,
        hxI, hxJ, mul_zero, φ.map_zero_eq_one, mul_one] at hh
      change ψ (Ideal.Quotient.mk I (a*b)) = 1
      simpa only [(Ideal.Quotient.mk I).map_mul] using hh
    · intro b
      obtain ⟨x, hxI, hxJ⟩ := hsep 0 (Ideal.Quotient.mk J b)
      have hh := ha x
      change ψ (Ideal.Quotient.mk I (a*x)) * φ (Ideal.Quotient.mk J (a*x)) = 1 at hh
      rw [(Ideal.Quotient.mk I).map_mul, (Ideal.Quotient.mk J).map_mul,
        hxI, hxJ, mul_zero, ψ.map_zero_eq_one, one_mul] at hh
      change φ (Ideal.Quotient.mk J (a*b)) = 1
      simpa only [(Ideal.Quotient.mk J).map_mul] using hh
  · rintro ⟨hψ,hφ⟩ x
    change ∀ b, ψ (Ideal.Quotient.mk I (a*b)) = 1 at hψ
    change ∀ b, φ (Ideal.Quotient.mk J (a*b)) = 1 at hφ
    change ψ (Ideal.Quotient.mk I (a*x)) * φ (Ideal.Quotient.mk J (a*x)) = 1
    rw [hψ x, hφ x, one_mul]

theorem coprime_superideals_inf_eq_iff {R : Type*} [CommRing R]
    (I J C D : Ideal R) (h : IsCoprime I J) (hIC : I ≤ C) (hJD : J ≤ D) :
    C ⊓ D = I ⊓ J ↔ C = I ∧ D = J := by
  have hleft (I J C D : Ideal R) (h : IsCoprime I J) (hJD : J ≤ D)
      (he : C ⊓ D = I ⊓ J) : C ≤ I := by
    intro a ha
    obtain ⟨i, hi, j, hj, hij⟩ := h.exists
    have hai : a*i ∈ I := I.mul_mem_left a hi
    have haj : a*j ∈ C ⊓ D :=
      ⟨C.mul_mem_right j ha, hJD (J.mul_mem_left a hj)⟩
    rw [he] at haj
    have hs := I.add_mem hai haj.1
    simpa only [← mul_add, hij, mul_one] using hs
  constructor
  · intro he
    refine ⟨le_antisymm (hleft I J C D h hJD he) hIC, ?_⟩
    apply le_antisymm _ hJD
    exact hleft J I D C h.symm hIC (by simpa only [inf_comm] using he)
  · rintro ⟨rfl,rfl⟩
    rfl

theorem quotientCharacterConductor_crt_exact_iff {R : Type*} [CommRing R]
    (I J : Ideal R) (h : IsCoprime I J)
    (ψ : AddChar (R ⧸ I) ℂ) (φ : AddChar (R ⧸ J) ℂ) :
    quotientCharacterConductor (I*J) (crtAddCharEquiv I J h (ψ,φ)) = I*J ↔
      quotientCharacterConductor I ψ = I ∧ quotientCharacterConductor J φ = J := by
  rw [quotientCharacterConductor_crt, ← Ideal.inf_eq_mul_of_isCoprime h]
  exact coprime_superideals_inf_eq_iff I J _ _ h
    (ideal_le_quotientCharacterConductor I ψ) (ideal_le_quotientCharacterConductor J φ)

/-- Literal exact-conductor complete-sum coefficients multiply for coprime ideals. -/
theorem primitiveConductorCharacterSum_mul {R : Type*} [CommRing R]
    (I J : Ideal R) (h : IsCoprime I J)
    [Fintype (R ⧸ I)] [Fintype (R ⧸ J)] [Fintype (R ⧸ I*J)]
    (k s : ℕ) (b : R) :
    (∑ χ ∈ primitiveConductorCharacters (I*J),
      finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk (I*J) b) χ) =
      (∑ ψ ∈ primitiveConductorCharacters I,
        finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk I b) ψ) *
      (∑ φ ∈ primitiveConductorCharacters J,
        finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk J b) φ) := by
  unfold primitiveConductorCharacters
  simp only [Finset.sum_filter]
  rw [← (crtAddCharEquiv I J h).bijective.sum_comp]
  simp only [quotientCharacterConductor_crt_exact_iff,
    finiteRingPowerCharacterTerm_crt, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro φ _
  split_ifs <;> simp_all

end WaringSiegel

#print axioms WaringSiegel.primitiveConductorCharacterSum_mul
