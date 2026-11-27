import WaringSiegel.WSL3TraceConductorCharacters

/-! # WSL3: exact finite ideal-duality on the rational trace torus -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
open NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem traceRationalPoint_sub (γ δ : K) :
    traceRationalPoint (γ-δ) = traceRationalPoint γ - traceRationalPoint δ := by
  simp only [traceRationalPoint, map_sub, Submodule.Quotient.mk_sub]

theorem trace_rational_characters_separate (γ δ : K)
    (h : ∀ x : 𝓞 K, traceTorusCharacter x (traceRationalPoint γ) =
      traceTorusCharacter x (traceRationalPoint δ)) :
    traceRationalPoint γ = traceRationalPoint δ := by
  apply (traceRationalPoint_eq_iff γ δ).mpr
  apply (trace_rational_characters_trivial_iff (γ-δ)).mp
  intro x
  rw [traceRationalPoint_sub]
  change (traceTorusAddChar x) (traceRationalPoint γ - traceRationalPoint δ) = 1
  rw [AddChar.map_sub_eq_div]
  change traceTorusCharacter x (traceRationalPoint γ) /
    traceTorusCharacter x (traceRationalPoint δ) = 1
  rw [h x]
  exact div_self (AddChar.val_isUnit (traceTorusAddChar x) (traceRationalPoint δ)).ne_zero

/-- The actual rational classes whose conductor divides a fixed ideal. -/
def traceIdealCenters (I : Ideal (𝓞 K)) : Set (ArchimedeanTraceTorus K) :=
  {q | ∃ γ : K, traceRationalPoint γ = q ∧ I ≤ traceConductor γ}

theorem ideal_le_traceIdealCenter_kernel (I : Ideal (𝓞 K)) (q : traceIdealCenters I) :
    I.toAddSubgroup ≤ (traceFrequencyAddChar (q : ArchimedeanTraceTorus K)).toAddMonoidHom.ker := by
  obtain ⟨γ, hγ, hI⟩ := q.property
  intro x hx
  change traceTorusCharacter x q = 1
  rw [← hγ]
  rw [← traceFrequencyAddChar_idealConductor] at hI
  have h := hI hx (1 : 𝓞 K)
  simpa only [mul_one] using h

def traceIdealAddChar (I : Ideal (𝓞 K)) (q : traceIdealCenters I) :
    AddChar (𝓞 K ⧸ I) ℂ := by
  let f : (𝓞 K ⧸ I) →+ Additive ℂ := QuotientAddGroup.lift I.toAddSubgroup
    (traceFrequencyAddChar (q : ArchimedeanTraceTorus K)).toAddMonoidHom
    (ideal_le_traceIdealCenter_kernel I q)
  exact AddChar.toAddMonoidHomEquiv.symm f

@[simp] theorem traceIdealAddChar_mk (I : Ideal (𝓞 K)) (q : traceIdealCenters I) (x : 𝓞 K) :
    traceIdealAddChar I q (Ideal.Quotient.mk I x) = traceTorusCharacter x q := rfl

theorem traceIdealAddChar_injective (I : Ideal (𝓞 K)) :
    Function.Injective (traceIdealAddChar I) := by
  intro q r h
  obtain ⟨γ, hγ, -⟩ := q.property
  obtain ⟨δ, hδ, -⟩ := r.property
  apply Subtype.ext
  rw [← hγ, ← hδ]
  apply trace_rational_characters_separate
  intro x
  rw [hγ, hδ]
  exact congrArg (fun χ : AddChar (𝓞 K ⧸ I) ℂ => χ (Ideal.Quotient.mk I x)) h

theorem traceIdealAddChar_surjective (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Function.Surjective (traceIdealAddChar I) := by
  intro ψ
  obtain ⟨γ, hcond, hγ⟩ := ideal_character_has_rational_trace_representative I hI ψ
  refine ⟨⟨traceRationalPoint γ, γ, rfl, hcond⟩, ?_⟩
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (hγ a).symm

def traceIdealCharacterEquiv (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    traceIdealCenters I ≃ AddChar (𝓞 K ⧸ I) ℂ :=
  Equiv.ofBijective (traceIdealAddChar I)
    ⟨traceIdealAddChar_injective I, traceIdealAddChar_surjective I hI⟩

theorem traceIdealCenters_card (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Nat.card (traceIdealCenters I) = Ideal.absNorm I := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI := Fintype.ofFinite (𝓞 K ⧸ I)
  rw [Nat.card_congr (traceIdealCharacterEquiv I hI), Nat.card_eq_fintype_card,
    AddChar.card_eq, ← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
  rfl

theorem traceIdealCenters_finite (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Finite (traceIdealCenters I) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot I hI
  exact Finite.of_injective (traceIdealAddChar I) (traceIdealAddChar_injective I)

end WaringSiegel

#print axioms WaringSiegel.traceIdealCharacterEquiv
#print axioms WaringSiegel.traceIdealCenters_card
