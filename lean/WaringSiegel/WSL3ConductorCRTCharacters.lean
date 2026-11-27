import WaringSiegel.WSL3LocalConductorSeries
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # WSL3: character and complete-sum factorization under the actual CRT -/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel

def productAddChar {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ψ : AddChar A ℂ) (φ : AddChar B ℂ) : AddChar (A × B) ℂ where
  toFun x := ψ x.1 * φ x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

def productAddCharEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] :
    AddChar A ℂ × AddChar B ℂ ≃ AddChar (A × B) ℂ where
  toFun ψ := productAddChar ψ.1 ψ.2
  invFun χ :=
    (χ.compAddMonoidHom
      { toFun := fun x => (x,0)
        map_zero' := rfl
        map_add' := by intros; simp },
     χ.compAddMonoidHom
      { toFun := fun x => (0,x)
        map_zero' := rfl
        map_add' := by intros; simp })
  left_inv := by
    intro ψ
    apply Prod.ext <;> ext x <;> simp [productAddChar, AddChar.compAddMonoidHom_apply]
  right_inv := by
    intro χ
    ext x
    change χ (x.1,0) * χ (0,x.2) = χ x
    rw [← χ.map_add_eq_mul]
    congr 1
    ext <;> simp

def ringEquivAddCharEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : AddChar S ℂ ≃ AddChar R ℂ where
  toFun ψ := ψ.compAddMonoidHom e.toRingHom.toAddMonoidHom
  invFun ψ := ψ.compAddMonoidHom e.symm.toRingHom.toAddMonoidHom
  left_inv := by intro ψ; ext x; exact congrArg ψ (e.apply_symm_apply x)
  right_inv := by intro ψ; ext x; exact congrArg ψ (e.symm_apply_apply x)

theorem finiteRingPowerSum_product {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (k : ℕ) :
    finiteRingPowerSum (productAddChar ψ φ) k =
      finiteRingPowerSum ψ k * finiteRingPowerSum φ k := by
  change (∑ x : R × S, ψ (x.1^k) * φ (x.2^k)) = _
  rw [Fintype.sum_prod_type]
  unfold finiteRingPowerSum
  rw [Finset.sum_mul_sum]

theorem finiteRingPowerCharacterTerm_product {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (ψ : AddChar R ℂ) (φ : AddChar S ℂ)
    (k s : ℕ) (b : R × S) :
    finiteRingPowerCharacterTerm k s b (productAddChar ψ φ) =
      finiteRingPowerCharacterTerm k s b.1 ψ * finiteRingPowerCharacterTerm k s b.2 φ := by
  unfold finiteRingPowerCharacterTerm
  rw [finiteRingPowerSum_product]
  simp only [Fintype.card_prod, Nat.cast_mul, mul_div_mul_comm, mul_pow,
    productAddChar, AddChar.coe_mk, Prod.fst_neg, Prod.snd_neg]
  ring

def crtAddCharEquiv {R : Type*} [CommRing R] (I J : Ideal R) (h : IsCoprime I J) :
    AddChar (R ⧸ I) ℂ × AddChar (R ⧸ J) ℂ ≃ AddChar (R ⧸ I*J) ℂ :=
  productAddCharEquiv.trans (ringEquivAddCharEquiv (Ideal.quotientMulEquivQuotientProd I J h))

@[simp] theorem crtAddCharEquiv_mk {R : Type*} [CommRing R]
    (I J : Ideal R) (h : IsCoprime I J)
    (ψ : AddChar (R ⧸ I) ℂ) (φ : AddChar (R ⧸ J) ℂ) (x : R) :
    crtAddCharEquiv I J h (ψ,φ) (Ideal.Quotient.mk (I*J) x) =
      ψ (Ideal.Quotient.mk I x) * φ (Ideal.Quotient.mk J x) := by
  rfl

theorem finiteRingPowerCharacterTerm_crt {R : Type*} [CommRing R]
    (I J : Ideal R) (h : IsCoprime I J)
    [Fintype (R ⧸ I)] [Fintype (R ⧸ J)] [Fintype (R ⧸ I*J)]
    (ψ : AddChar (R ⧸ I) ℂ) (φ : AddChar (R ⧸ J) ℂ) (k s : ℕ) (b : R) :
    finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk (I*J) b)
      (crtAddCharEquiv I J h (ψ,φ)) =
      finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk I b) ψ *
        finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk J b) φ := by
  change finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk (I*J) b)
    ((productAddChar ψ φ).compAddMonoidHom
      (Ideal.quotientMulEquivQuotientProd I J h).toRingHom.toAddMonoidHom) = _
  rw [finite_ring_power_character_term_inflation
    (Ideal.quotientMulEquivQuotientProd I J h).toRingHom
    (Ideal.quotientMulEquivQuotientProd I J h).surjective]
  exact finiteRingPowerCharacterTerm_product ψ φ k s _

end WaringSiegel
