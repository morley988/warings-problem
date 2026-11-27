import WaringSiegel.WSL3TraceCharacterDuality

/-! # WSL3: the actual trace conductor of a finite residue character -/
noncomputable section
open scoped BigOperators Classical NumberField
open NumberField
namespace WaringSiegel

/-- The largest ideal on which a character, together with every multiplicative
translate, is trivial. -/
def addCharIdealConductor {R : Type*} [CommRing R] (ψ : AddChar R ℂ) : Ideal R where
  carrier := {a | ∀ x : R, ψ (a*x) = 1}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro a b ha hb x
    rw [add_mul, ψ.map_add_eq_mul, ha x, hb x, one_mul]
  smul_mem' := by
    intro r a ha x
    change ψ ((r*a)*x) = 1
    rw [mul_assoc, mul_left_comm r a x]
    exact ha (r*x)

variable {K : Type*} [Field K] [NumberField K]

theorem trace_rational_character_eq_one_iff (x : 𝓞 K) (γ : K) :
    traceTorusCharacter x (traceRationalPoint γ) = 1 ↔
      ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ K ((x : K)*γ) := by
  unfold traceRationalPoint
  rw [traceTorusCharacter_mk, ← map_mul, archimedeanTrace_field, traceExp_eq_one_iff_integer]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by exact_mod_cast hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by exact_mod_cast hn⟩

theorem trace_rational_characters_trivial_iff (γ : K) :
    (∀ x : 𝓞 K, traceTorusCharacter x (traceRationalPoint γ) = 1) ↔
      γ ∈ inverseDifferent K := by
  simp only [trace_rational_character_eq_one_iff]
  exact (mem_inverseDifferent_iff_trace_integral K γ).symm

/-- The abstract character conductor agrees exactly with the manuscript's
inverse-different conductor ideal. -/
theorem traceFrequencyAddChar_idealConductor (γ : K) :
    addCharIdealConductor (traceFrequencyAddChar (traceRationalPoint γ)) =
      traceConductor γ := by
  ext a
  change (∀ x : 𝓞 K, traceTorusCharacter (a*x) (traceRationalPoint γ) = 1) ↔
    (a : K)*γ ∈ inverseDifferent K
  simp only [traceTorusCharacter_mul, traceTorusMul_traceRationalPoint]
  exact trace_rational_characters_trivial_iff _

/-- Every character of an arbitrary nonzero ideal quotient comes from a field
center whose trace conductor divides that ideal. -/
theorem ideal_character_has_rational_trace_representative
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (ψ : AddChar (𝓞 K ⧸ I) ℂ) :
    ∃ γ : K, I ≤ traceConductor γ ∧
      ∀ x : 𝓞 K, ψ (Ideal.Quotient.mk I x) =
        traceTorusCharacter x (traceRationalPoint γ) := by
  let a : 𝓞 K := Ideal.absNorm I
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp hI)
  have hspan : Ideal.span ({a} : Set (𝓞 K)) ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.absNorm_mem I
  let ψ' : AddChar (PrincipalResidueRing a) ℂ :=
    ψ.compAddMonoidHom (Ideal.Quotient.factor hspan).toAddMonoidHom
  obtain ⟨γ, -, hγ⟩ := principal_character_has_rational_trace_representative a ha ψ'
  have he (x : 𝓞 K) : ψ (Ideal.Quotient.mk I x) =
      traceTorusCharacter x (traceRationalPoint γ) := by
    exact hγ x
  refine ⟨γ, ?_, he⟩
  rw [← traceFrequencyAddChar_idealConductor]
  intro b hb
  change ∀ x : 𝓞 K, traceTorusCharacter (b*x) (traceRationalPoint γ) = 1
  intro x
  rw [← he]
  have hbx : Ideal.Quotient.mk I (b*x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right x hb)
  rw [hbx, ψ.map_zero_eq_one]

end WaringSiegel

#print axioms WaringSiegel.traceFrequencyAddChar_idealConductor
#print axioms WaringSiegel.ideal_character_has_rational_trace_representative
