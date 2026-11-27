import WaringLinear.IdealPowerFibres

/-! # Small-conductor Gram estimates in an ideal quotient

The geometric input below counts input nodes in one ordinary residue class.
The arithmetic multiplicity of the power map is supplied by the ideal
factorization theorem.
-/
noncomputable section
open scoped BigOperators Classical NumberField
open UniqueFactorizationMonoid
open WaringSiegel WaringSiegel.WSL2

namespace WaringLinear

theorem count_composite_fibre {X Y Z : Type*} [Finite X] [Finite Y]
    (f : X → Y) (g : Y → Z) (b : Z) (L M : ℕ)
    (hf : ∀ y, Nat.card {x // f x=y} ≤ L)
    (hg : Nat.card {y // g y=b} ≤ M) :
    Nat.card {x // g (f x)=b} ≤ L*M := by
  letI := Fintype.ofFinite {y // g y=b}
  let e : {x // g (f x)=b} ≃ Σ y : {y // g y=b}, {x // f x=y.val} :=
    { toFun := fun x => ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
      invFun := fun z => ⟨z.2.val, by rw [z.2.property,z.1.property]⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨y,hy⟩,⟨x,hx⟩⟩; change f x = y at hx; subst y; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  calc
    _ ≤ ∑ _y : {y // g y=b}, L := Finset.sum_le_sum (fun y _ => hf y.val)
    _ = L*Nat.card {y // g y=b} := by simp [Nat.card_eq_fintype_card,mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left L hg

theorem unit_power_fibre_le (R : Type*) [CommRing R] [Fintype R] (k : ℕ) (b : R) :
    Nat.card {u : Rˣ // (u:R)^k=b} ≤ unitRootsCount R k := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [unitRootsCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert unit_power_fiber_card_le k b using 1
  congr 1
  ext u
  simp [unitPowerKernel, powerKernel]

variable {K X J : Type*} [Field K] [NumberField K] [Fintype X] [Fintype J]

theorem ideal_sampled_character_synthesis
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) (k L : ℕ) (hk : 0 < k)
    (hgood : ∀ P ∈ (normalizedFactors I).toFinset, (k : 𝓞 K) ∉ P)
    (r : X → (𝓞 K ⧸ I)ˣ) (hL : ∀ z, Nat.card {x : X // r x=z} ≤ L)
    (χ : J → AddChar (𝓞 K ⧸ I) ℂ) (hχ : Function.Injective χ) (w : J → ℂ) :
    (∑ x, ‖∑ j, w j * χ j ((r x : 𝓞 K ⧸ I)^k)‖^2) ≤
      ((L*k^(normalizedFactors I).toFinset.card*Ideal.absNorm I : ℕ) : ℝ) *
        ∑ j, ‖w j‖^2 := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI := Fintype.ofFinite (𝓞 K ⧸ I)
  have hnorm : Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [← Nat.card_eq_fintype_card,Ideal.absNorm_apply]
    rfl
  have h := sampled_character_synthesis (fun x : X => (r x : 𝓞 K ⧸ I)^k)
    (L*k^(normalizedFactors I).toFinset.card)
    (fun b => count_composite_fibre r (fun u : (𝓞 K ⧸ I)ˣ => (u : 𝓞 K ⧸ I)^k) b L _
      hL ((unit_power_fibre_le _ k b).trans (ideal_unitRootsCount_le I hI k hk hgood))) χ hχ w
  simpa only [Nat.cast_mul,hnorm] using h

#print axioms ideal_sampled_character_synthesis

end WaringLinear
