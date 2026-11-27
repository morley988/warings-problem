import WaringSiegel.WSL3LocalCharacterCount

/-! # WSL3: normalized complete sums are invariant under quotient inflation -/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel

theorem finite_average_surjective_addHom
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) (g : B → ℂ) :
    (∑ x : A, g (f x)) / (Fintype.card A : ℂ) =
      (∑ y : B, g y) / (Fintype.card B : ℂ) := by
  have hA : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hleft (y : B) : (∑ x : A, g (f x + y)) = ∑ x : A, g (f x) := by
    obtain ⟨z, rfl⟩ := hf y
    have h := (Equiv.addRight z).bijective.sum_comp (fun x : A => g (f x))
    change (∑ x : A, g (f (x + z))) = ∑ x : A, g (f x) at h
    simpa only [map_add] using h
  have hright (x : A) : (∑ y : B, g (f x + y)) = ∑ y : B, g y :=
    (Equiv.addLeft (f x)).bijective.sum_comp g
  have hdouble : (Fintype.card B : ℂ) * (∑ x : A, g (f x)) =
      (Fintype.card A : ℂ) * (∑ y : B, g y) := by
    calc
      _ = ∑ y : B, ∑ x : A, g (f x + y) := by
        simp only [hleft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ x : A, ∑ y : B, g (f x + y) := Finset.sum_comm
      _ = _ := by simp only [hright, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply (div_eq_div_iff hA hB).mpr
  linear_combination hdouble

theorem finite_ring_power_sum_inflation
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (f : R →+* S) (hf : Function.Surjective f) (ψ : AddChar S ℂ) (k : ℕ) :
    finiteRingPowerSum (ψ.compAddMonoidHom f.toAddMonoidHom) k / (Fintype.card R : ℂ) =
      finiteRingPowerSum ψ k / (Fintype.card S : ℂ) := by
  simpa [finiteRingPowerSum, map_pow] using
    finite_average_surjective_addHom f.toAddMonoidHom hf (fun x : S => ψ (x^k))

theorem quotient_character_inflation_injective
    {R : Type*} [CommRing R] {I J : Ideal R} (hIJ : I ≤ J) :
    Function.Injective (fun ψ : AddChar (R ⧸ J) ℂ =>
      ψ.compAddMonoidHom (Ideal.Quotient.factor hIJ).toAddMonoidHom) := by
  intro ψ φ h
  ext y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.factor_surjective hIJ y
  exact congrArg (fun χ : AddChar (R ⧸ I) ℂ => χ x) h

def finiteRingPowerCharacterTerm
    {R : Type*} [CommRing R] [Fintype R] (k s : ℕ) (b : R) (ψ : AddChar R ℂ) : ℂ :=
  (finiteRingPowerSum ψ k / (Fintype.card R : ℂ))^s * ψ (-b)

theorem finite_ring_power_character_term_inflation
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (f : R →+* S) (hf : Function.Surjective f) (k s : ℕ) (b : R) (ψ : AddChar S ℂ) :
    finiteRingPowerCharacterTerm k s b (ψ.compAddMonoidHom f.toAddMonoidHom) =
      finiteRingPowerCharacterTerm k s (f b) ψ := by
  unfold finiteRingPowerCharacterTerm
  rw [finite_ring_power_sum_inflation f hf]
  simp [map_neg]

theorem finite_ring_noninflated_character_sum
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (f : R →+* S) (hf : Function.Surjective f) (k s : ℕ) (b : R) :
    (∑ ψ ∈ Finset.univ \ Finset.univ.image (fun φ : AddChar S ℂ =>
      φ.compAddMonoidHom f.toAddMonoidHom), finiteRingPowerCharacterTerm k s b ψ) =
      (∑ ψ : AddChar R ℂ, finiteRingPowerCharacterTerm k s b ψ) -
      ∑ φ : AddChar S ℂ, finiteRingPowerCharacterTerm k s (f b) φ := by
  let g := fun φ : AddChar S ℂ => φ.compAddMonoidHom f.toAddMonoidHom
  have hg : Function.Injective g := by
    intro ψ φ h
    ext y
    obtain ⟨x, rfl⟩ := hf y
    exact congrArg (fun χ : AddChar R ℂ => χ x) h
  have hs := Finset.sum_sdiff (f := finiteRingPowerCharacterTerm k s b)
    (Finset.subset_univ (Finset.univ.image g))
  rw [Finset.sum_image (fun _ _ _ _ h => hg h)] at hs
  simp only [g, finite_ring_power_character_term_inflation f hf] at hs
  exact eq_sub_iff_add_eq.mpr hs

end WaringSiegel
