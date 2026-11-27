import WaringSiegel.WSL4WeilCubic
import WaringSiegel.WSL3ConductorCRT

/-! # Primitive quotient characters and arbitrary linear twists

Orthogonality represents any additive character of a finite commutative ring
as a scalar shift of a primitive character.  Exact ideal conductor is exactly
the required primitive condition, so the later local argument needs no choice
of a principal generator for a global ideal or an inverse different.
-/

noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical

theorem exists_mulShift_eq_of_primitive_ring
    {A : Type*} [CommRing A] [Fintype A]
    (φ : AddChar A ℂ) (hφ : φ.IsPrimitive) (ψ : AddChar A ℂ) :
    ∃ a : A, φ.mulShift a = ψ := by
  by_contra h
  push_neg at h
  have hz : (∑ a : A, ∑ x : A, φ (a * x) * ψ (-x)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hn : φ.mulShift a * ψ⁻¹ ≠ 1 := fun he => h a (mul_inv_eq_one.mp he)
    simpa only [AddChar.mul_apply, AddChar.mulShift_apply, AddChar.inv_apply] using
      AddChar.sum_eq_zero_of_ne_one hn
  have hc : (∑ a : A, ∑ x : A, φ (a * x) * ψ (-x)) = (Fintype.card A : ℂ) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, AddChar.sum_mulShift _ hφ]
    simp
  rw [hc] at hz
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hz

theorem quotient_character_primitive_iff_exact_conductor
    {R : Type*} [CommRing R] (I : Ideal R) (ψ : AddChar (R ⧸ I) ℂ) :
    ψ.IsPrimitive ↔ quotientCharacterConductor I ψ = I := by
  constructor
  · intro hp
    apply le_antisymm _ (ideal_le_quotientCharacterConductor I ψ)
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    by_contra h
    apply hp h
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ha b
  · intro he a ha hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← he]
    intro x
    exact congrArg (fun χ : AddChar (R ⧸ I) ℂ => χ (Ideal.Quotient.mk I x)) hz

def mixedCubicSum {A : Type*} [CommRing A] [Fintype A]
    (ψ : AddChar A ℂ) (a b : A) : ℂ := ∑ x : A, ψ (a*x^3+b*x)

def twistedPowerSum {A : Type*} [CommRing A] [Fintype A]
    (ψ χ : AddChar A ℂ) (k : ℕ) : ℂ := ∑ x : A, ψ (x^k)*χ x

theorem twistedPowerSum_eq_mixedCubicSum
    {A : Type*} [CommRing A] [Fintype A] (ψ χ : AddChar A ℂ)
    (hψ : ψ.IsPrimitive) : ∃ b : A, twistedPowerSum ψ χ 3 = mixedCubicSum ψ 1 b := by
  obtain ⟨b, hb⟩ := exists_mulShift_eq_of_primitive_ring ψ hψ χ
  refine ⟨b, ?_⟩
  simp only [twistedPowerSum, mixedCubicSum, one_mul, ψ.map_add_eq_mul,
    ← hb, AddChar.mulShift_apply]

theorem mixedCubicSum_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
    (e : A ≃+* B) (ψ : AddChar B ℂ) (a b : A) :
    mixedCubicSum (ψ.compAddMonoidHom e.toAddMonoidHom) a b =
      mixedCubicSum ψ (e a) (e b) := by
  change (∑ x : A, ψ (e (a*x^3+b*x))) = ∑ x : B, ψ (e a*x^3+e b*x)
  simpa only [mixedCubicSum, AddChar.compAddMonoidHom_apply, map_add, map_mul, map_pow] using
    e.bijective.sum_comp (fun x : B => ψ (e a*x^3+e b*x))

theorem twistedPowerSum_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
    (e : A ≃+* B) (ψ χ : AddChar B ℂ) (k : ℕ) :
    twistedPowerSum (ψ.compAddMonoidHom e.toAddMonoidHom)
      (χ.compAddMonoidHom e.toAddMonoidHom) k = twistedPowerSum ψ χ k := by
  change (∑ x : A, ψ (e (x^k))*χ (e x)) = ∑ x : B, ψ (x^k)*χ x
  simpa only [twistedPowerSum, AddChar.compAddMonoidHom_apply, map_pow] using
    e.bijective.sum_comp (fun x : B => ψ (x^k)*χ x)

theorem twistedPowerSum_product
    {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
    (ψ χ : AddChar A ℂ) (φ η : AddChar B ℂ) (k : ℕ) :
    twistedPowerSum (productAddChar ψ φ) (productAddChar χ η) k =
      twistedPowerSum ψ χ k * twistedPowerSum φ η k := by
  change (∑ x : A × B, (ψ (x.1^k)*φ (x.2^k))*(χ x.1*η x.2)) = _
  unfold twistedPowerSum
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem twistedPowerSum_crt
    {R : Type*} [CommRing R] (I J : Ideal R) (h : IsCoprime I J)
    [Fintype (R ⧸ I)] [Fintype (R ⧸ J)] [Fintype (R ⧸ I*J)]
    (ψ χ : AddChar (R ⧸ I) ℂ) (φ η : AddChar (R ⧸ J) ℂ) (k : ℕ) :
    twistedPowerSum (crtAddCharEquiv I J h (ψ,φ))
      (crtAddCharEquiv I J h (χ,η)) k =
        twistedPowerSum ψ χ k * twistedPowerSum φ η k := by
  change twistedPowerSum
    ((productAddChar ψ φ).compAddMonoidHom
      (Ideal.quotientMulEquivQuotientProd I J h).toAddMonoidHom)
    ((productAddChar χ η).compAddMonoidHom
      (Ideal.quotientMulEquivQuotientProd I J h).toAddMonoidHom) k = _
  rw [twistedPowerSum_ringEquiv]
  exact twistedPowerSum_product ψ χ φ η k

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.quotient_character_primitive_iff_exact_conductor
#print axioms WaringSiegel.WSL4Weil.twistedPowerSum_crt
