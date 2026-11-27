import WaringSiegel.WSL3AuxiliaryCompleteSums

/-! # WSL3: exact masked complete-sum products and common-modulus normalization -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel

theorem finite_scaled_power_average_inflation
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (f : R →+* S) (hf : Function.Surjective f) (ψ : AddChar S ℂ) (k : ℕ) (p : R) :
    finiteRingScaledPowerSum (ψ.compAddMonoidHom f.toAddMonoidHom) k p /
        (Fintype.card R : ℂ) =
      finiteRingScaledPowerSum ψ k (f p) / (Fintype.card S : ℂ) := by
  change (∑ x : R, ψ (f ((p*x)^k))) / (Fintype.card R : ℂ) = _
  simp only [f.map_pow, f.map_mul]
  exact finite_average_surjective_addHom f.toAddMonoidHom hf (fun x : S => ψ ((f p*x)^k))

theorem finiteMaskedPowerSum_product
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Fintype R] [Fintype S]
    (f : R →+* A) (g : S →+* B) (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (k : ℕ) :
    finiteMaskedPowerSum (RingHom.prodMap f g) (productAddChar ψ φ) k =
      finiteMaskedPowerSum f ψ k * finiteMaskedPowerSum g φ k := by
  unfold finiteMaskedPowerSum
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change (if IsUnit (f x,g y) then ψ (x^k)*φ (y^k) else 0) = _
  simp only [Prod.isUnit_iff]
  by_cases hx : IsUnit (f x) <;> by_cases hy : IsUnit (g y) <;> simp [hx,hy]

theorem finiteRingScaledPowerSum_product
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (k : ℕ) (p : R × S) :
    finiteRingScaledPowerSum (productAddChar ψ φ) k p =
      finiteRingScaledPowerSum ψ k p.1 * finiteRingScaledPowerSum φ k p.2 := by
  change (∑ x : R × S, ψ ((p.1*x.1)^k)*φ ((p.2*x.2)^k)) = _
  rw [Fintype.sum_prod_type]
  unfold finiteRingScaledPowerSum
  rw [Finset.sum_mul_sum]

def finiteMaskedCubicCharacterTerm
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R]
    (f : R →+* S) (p b : R) (ψ : AddChar R ℂ) : ℂ :=
  (finiteMaskedPowerSum f ψ 3 / (Fintype.card R : ℂ))^4 *
    (finiteRingScaledPowerSum ψ 3 p / (Fintype.card R : ℂ))^4 * ψ (-b)

theorem finiteMaskedCubicCharacterTerm_product
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Fintype R] [Fintype S]
    (f : R →+* A) (g : S →+* B) (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (p b : R × S) :
    finiteMaskedCubicCharacterTerm (RingHom.prodMap f g) p b (productAddChar ψ φ) =
      finiteMaskedCubicCharacterTerm f p.1 b.1 ψ * finiteMaskedCubicCharacterTerm g p.2 b.2 φ := by
  unfold finiteMaskedCubicCharacterTerm
  rw [finiteMaskedPowerSum_product, finiteRingScaledPowerSum_product]
  simp only [Fintype.card_prod, Nat.cast_mul, mul_div_mul_comm, mul_pow,
    productAddChar, AddChar.coe_mk, Prod.fst_neg, Prod.snd_neg]
  ring

theorem finiteMaskedCubicCharacterTerm_inflation
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Fintype R] [Fintype S]
    (f : R →+* S) (hf : Function.Surjective f) (g : S →+* T)
    (ψ : AddChar S ℂ) (p b : R) :
    finiteMaskedCubicCharacterTerm (g.comp f) p b (ψ.compAddMonoidHom f.toAddMonoidHom) =
      finiteMaskedCubicCharacterTerm g (f p) (f b) ψ := by
  unfold finiteMaskedCubicCharacterTerm
  rw [finite_masked_power_average_inflation f hf, finite_scaled_power_average_inflation f hf]
  congr 2
  change ψ (f (-b)) = ψ (-(f b))
  rw [f.map_neg]

variable {K : Type*} [Field K] [NumberField K]

/-- Both normalized factors may be evaluated on the actual common modulus.
This is the literal masked/scaled term to which CRT applies. -/
theorem auxiliaryCubicCharacterContribution_common_modulus
    (c : CubicConductorCharacter K) (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    let M := auxiliaryCommonModulus c.1.1 p
    letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
    let f : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ c.1.1) := Ideal.Quotient.factor inf_le_left
    let g : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ Ideal.span ({p} : Set (𝓞 K))) := Ideal.Quotient.factor inf_le_right
    auxiliaryCubicCharacterContribution c p hp ν =
      finiteMaskedCubicCharacterTerm g (Ideal.Quotient.mk M p) (Ideal.Quotient.mk M ν)
        (c.2.1.compAddMonoidHom f.toAddMonoidHom) := by
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  letI := idealResidueFintype c.1.1 c.1.2
  let f : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ c.1.1) := Ideal.Quotient.factor inf_le_left
  let g : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ Ideal.span ({p} : Set (𝓞 K))) := Ideal.Quotient.factor inf_le_right
  change auxiliaryMaskedCubicAverage c p hp ^4 * auxiliaryScaledCubicAverage c p ^4 *
    c.2.1 (-Ideal.Quotient.mk c.1.1 ν) =
    finiteMaskedCubicCharacterTerm g (Ideal.Quotient.mk M p) (Ideal.Quotient.mk M ν)
      (c.2.1.compAddMonoidHom f.toAddMonoidHom)
  unfold finiteMaskedCubicCharacterTerm
  rw [finite_scaled_power_average_inflation f (Ideal.Quotient.factor_surjective inf_le_left)]
  rfl

end WaringSiegel
#print axioms WaringSiegel.auxiliaryCubicCharacterContribution_common_modulus
#print axioms WaringSiegel.finiteMaskedCubicCharacterTerm_product
