import WaringSiegel.WSL3LocalCharacterCount
import WaringSiegel.WSL2LocalOriginalModified

/-! # WSL3: literal restricted and scaled cubic counts have exact finite Fourier expansions -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel

variable {R : Type*} [CommRing R] [Fintype R]

def finiteRingUnitPowerSum (ψ : AddChar R ℂ) (k : ℕ) : ℂ :=
  ∑ x : Rˣ, ψ ((x : R)^k)

def finiteRingScaledPowerSum (ψ : AddChar R ℂ) (k : ℕ) (p : R) : ℂ :=
  ∑ x : R, ψ ((p*x)^k)

theorem finite_two_family_power_sum_expansion
    {A B : Type*} [Fintype A] [Fintype B] (f : A → R) (g : B → R)
    (ψ : AddChar R ℂ) (s t : ℕ) (b : R) :
    (∑ a : A, ψ (f a))^s * (∑ a : B, ψ (g a))^t * ψ (-b) =
      ∑ x : (Fin s → A) × (Fin t → B),
        ψ ((∑ i, f (x.1 i)) + (∑ i, g (x.2 i)) - b) := by
  rw [Fintype.sum_pow, Fintype.sum_pow, Fintype.sum_prod_type]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [← ring_addChar_sum, ← ring_addChar_sum, ← ψ.map_add_eq_mul,
    ← ψ.map_add_eq_mul, sub_eq_add_neg]

theorem finite_two_family_power_character_count
    {A B : Type*} [Fintype A] [Fintype B] (f : A → R) (g : B → R)
    (s t : ℕ) (b : R) :
    (∑ ψ : AddChar R ℂ, (∑ a : A, ψ (f a))^s *
      (∑ a : B, ψ (g a))^t * ψ (-b)) =
      (Fintype.card R : ℂ) *
        (Nat.card {x : (Fin s → A) × (Fin t → B) //
          (∑ i, f (x.1 i)) + (∑ i, g (x.2 i)) = b} : ℂ) := by
  simp only [finite_two_family_power_sum_expansion]
  rw [Finset.sum_comm]
  simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

def finiteRingRestrictedCubicCharacterTerm (p b : R) (ψ : AddChar R ℂ) : ℂ :=
  (finiteRingUnitPowerSum ψ 3 / (Fintype.card R : ℂ))^4 *
    (finiteRingScaledPowerSum ψ 3 p / (Fintype.card R : ℂ))^4 * ψ (-b)

theorem finite_restricted_cubic_character_formula (p b : R) :
    (∑ ψ : AddChar R ℂ, finiteRingRestrictedCubicCharacterTerm p b ψ) =
      (Nat.card {x : (Fin 4 → Rˣ) × (Fin 4 → R) //
        (∑ i, (x.1 i : R)^3) + (∑ i, (p*x.2 i)^3) = b} : ℂ) /
        (Fintype.card R : ℂ)^7 := by
  have hq : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold finiteRingRestrictedCubicCharacterTerm finiteRingUnitPowerSum finiteRingScaledPowerSum
  have he (ψ : AddChar R ℂ) :
      ((∑ x : Rˣ, ψ ((x : R)^3)) / (Fintype.card R : ℂ))^4 *
      ((∑ x : R, ψ ((p*x)^3)) / (Fintype.card R : ℂ))^4 * ψ (-b) =
      ((∑ x : Rˣ, ψ ((x : R)^3))^4 * (∑ x : R, ψ ((p*x)^3))^4 * ψ (-b)) /
        (Fintype.card R : ℂ)^8 := by field_simp
  simp only [he]
  rw [← Finset.sum_div, finite_two_family_power_character_count]
  field_simp

variable {S : Type*} [CommRing S]

def unitCubicTuplesEquivRestricted (I : Ideal S) (p a : S) :
    {x : (Fin 4 → (S ⧸ I)ˣ) × (Fin 4 → S ⧸ I) //
      (∑ i, (x.1 i : S ⧸ I)^3) + (∑ i, (Ideal.Quotient.mk I p*x.2 i)^3) =
        Ideal.Quotient.mk I a} ≃ RestrictedCubicSolutions S I p a where
  toFun x := ⟨(x.1.2, fun i => (x.1.1 i : S ⧸ I)), x.2, fun i => (x.1.1 i).isUnit⟩
  invFun x := ⟨(fun i => (x.2.2 i).unit, x.1.1), by
    simpa only [IsUnit.unit_spec] using x.2.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Units.ext
      exact IsUnit.unit_spec _
    · rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact (x.2.2 i).unit_spec

theorem original_restricted_cubic_character_formula (I : Ideal S) (p a : S)
    [Fintype (S ⧸ I)] :
    (∑ ψ : AddChar (S ⧸ I) ℂ,
      finiteRingRestrictedCubicCharacterTerm (Ideal.Quotient.mk I p) (Ideal.Quotient.mk I a) ψ) =
        (Nat.card (RestrictedCubicSolutions S I p a) : ℂ) / (Fintype.card (S ⧸ I) : ℂ)^7 := by
  rw [finite_restricted_cubic_character_formula,
    Nat.card_congr (unitCubicTuplesEquivRestricted I p a)]

variable {K : Type*} [Field K] [NumberField K]

theorem primePower_restricted_cubic_character_formula
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p a : 𝓞 K) (n : ℕ)
    [Fintype (𝓞 K ⧸ v.asIdeal^(n+1))] :
    (normalizedOriginalRestrictedCubicCount v p a n : ℂ) =
      ∑ ψ : AddChar (𝓞 K ⧸ v.asIdeal^(n+1)) ℂ,
        finiteRingRestrictedCubicCharacterTerm (Ideal.Quotient.mk (v.asIdeal^(n+1)) p)
          (Ideal.Quotient.mk (v.asIdeal^(n+1)) a) ψ := by
  rw [original_restricted_cubic_character_formula]
  have hc : Fintype.card (𝓞 K ⧸ v.asIdeal^(n+1)) = Ideal.absNorm (v.asIdeal^(n+1)) := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
    rfl
  unfold normalizedOriginalRestrictedCubicCount
  push_cast
  rw [hc, map_pow, Nat.cast_pow, ← pow_mul, Nat.mul_comm (n+1) 7]

end WaringSiegel
#print axioms WaringSiegel.primePower_restricted_cubic_character_formula
