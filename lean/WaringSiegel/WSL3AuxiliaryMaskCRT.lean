import WaringSiegel.WSL3AuxiliaryProductSums
import WaringSiegel.WSL2TraceResidueWeyl

/-! # WSL3: the actual quotient mask respects CRT and unit scaling -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel

theorem finiteMaskedPowerSum_mask_congr
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Fintype R]
    (f : R →+* A) (g : R →+* B) (h : ∀ x, IsUnit (f x) ↔ IsUnit (g x))
    (ψ : AddChar R ℂ) (k : ℕ) :
    finiteMaskedPowerSum f ψ k = finiteMaskedPowerSum g ψ k := by
  simp only [finiteMaskedPowerSum, h]

theorem finiteMaskedCubicCharacterTerm_mask_congr
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Fintype R]
    (f : R →+* A) (g : R →+* B) (h : ∀ x, IsUnit (f x) ↔ IsUnit (g x))
    (ψ : AddChar R ℂ) (p b : R) :
    finiteMaskedCubicCharacterTerm f p b ψ = finiteMaskedCubicCharacterTerm g p b ψ := by
  simp only [finiteMaskedCubicCharacterTerm, finiteMaskedPowerSum_mask_congr f g h]

theorem finiteMaskedPowerSum_id
    {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) (k : ℕ) :
    finiteMaskedPowerSum (RingHom.id R) ψ k = finiteRingUnitPowerSum ψ k := by
  classical
  unfold finiteMaskedPowerSum finiteRingUnitPowerSum
  calc
    _ = ∑ x : R, ∑ u : Rˣ, if x = (u : R) then ψ (x^k) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : IsUnit x
      · simp only [RingHom.id_apply, if_pos hx]
        simpa only [if_pos hx] using (sum_units_eq_isUnit x (ψ (x^k))).symm
      · simp only [RingHom.id_apply, if_neg hx]
        simpa only [if_neg hx] using (sum_units_eq_isUnit x (ψ (x^k))).symm
    _ = _ := by rw [Finset.sum_comm]; simp

theorem finiteMaskedCubicCharacterTerm_id
    {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) (p b : R) :
    finiteMaskedCubicCharacterTerm (RingHom.id R) p b ψ =
      finiteRingRestrictedCubicCharacterTerm p b ψ := by
  simp only [finiteMaskedCubicCharacterTerm, finiteMaskedPowerSum_id,
    finiteRingRestrictedCubicCharacterTerm]

theorem finiteMaskedPowerSum_subsingleton
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Subsingleton S]
    (f : R →+* S) (ψ : AddChar R ℂ) (k : ℕ) :
    finiteMaskedPowerSum f ψ k = finiteRingPowerSum ψ k := by
  have hu (x : R) : IsUnit (f x) := by
    have he : f x = 1 := Subsingleton.elim _ _
    rw [he]
    exact isUnit_one
  simp only [finiteMaskedPowerSum, hu, if_true, finiteRingPowerSum]

theorem finiteRingScaledPowerSum_of_isUnit
    {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) (k : ℕ)
    (p : R) (hp : IsUnit p) :
    finiteRingScaledPowerSum ψ k p = finiteRingPowerSum ψ k := by
  obtain ⟨u,rfl⟩ := hp
  exact (Units.mulLeft u).bijective.sum_comp (fun x : R => ψ (x^k))

theorem finiteMaskedCubicCharacterTerm_unrestricted
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Subsingleton S]
    (f : R →+* S) (ψ : AddChar R ℂ) (p b : R) (hp : IsUnit p) :
    finiteMaskedCubicCharacterTerm f p b ψ = finiteRingPowerCharacterTerm 3 8 b ψ := by
  simp only [finiteMaskedCubicCharacterTerm, finiteMaskedPowerSum_subsingleton,
    finiteRingScaledPowerSum_of_isUnit ψ 3 p hp, finiteRingPowerCharacterTerm]
  ring

/-- CRT respects the actual unit condition in a coarser quotient. The mask
need not impose units at all primes of the complete-sum modulus. -/
theorem finiteMaskedCubicCharacterTerm_crt
    {R : Type*} [CommRing R]
    (I J A B : Ideal R) (h : IsCoprime I J) (hIA : I ≤ A) (hJB : J ≤ B)
    [Fintype (R ⧸ I)] [Fintype (R ⧸ J)] [Fintype (R ⧸ I*J)]
    (ψ : AddChar (R ⧸ I) ℂ) (φ : AddChar (R ⧸ J) ℂ) (p b : R) :
    finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor (mul_le_mul' hIA hJB))
      (Ideal.Quotient.mk (I*J) p) (Ideal.Quotient.mk (I*J) b)
      (crtAddCharEquiv I J h (ψ,φ)) =
      finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hIA)
        (Ideal.Quotient.mk I p) (Ideal.Quotient.mk I b) ψ *
      finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hJB)
        (Ideal.Quotient.mk J p) (Ideal.Quotient.mk J b) φ := by
  have hAB : IsCoprime A B := by
    obtain ⟨i,hi,j,hj,hij⟩ := h.exists
    exact Ideal.isCoprime_iff_exists.mpr ⟨i,hIA hi,j,hJB hj,hij⟩
  let e := Ideal.quotientMulEquivQuotientProd I J h
  let d := Ideal.quotientMulEquivQuotientProd A B hAB
  let g := RingHom.prodMap (Ideal.Quotient.factor hIA) (Ideal.Quotient.factor hJB)
  have hm (x : R ⧸ I*J) :
      IsUnit (Ideal.Quotient.factor (mul_le_mul' hIA hJB) x) ↔
        IsUnit ((g.comp e.toRingHom) x) := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (MulEquiv.isUnit_map (f := d.toMulEquiv)).symm
  rw [finiteMaskedCubicCharacterTerm_mask_congr _ _ hm]
  change finiteMaskedCubicCharacterTerm (g.comp e.toRingHom)
    (Ideal.Quotient.mk (I*J) p) (Ideal.Quotient.mk (I*J) b)
    ((productAddChar ψ φ).compAddMonoidHom e.toRingHom.toAddMonoidHom) = _
  rw [finiteMaskedCubicCharacterTerm_inflation e.toRingHom e.surjective]
  exact finiteMaskedCubicCharacterTerm_product _ _ ψ φ _ _

end WaringSiegel
#print axioms WaringSiegel.finiteMaskedCubicCharacterTerm_crt
#print axioms WaringSiegel.finiteMaskedCubicCharacterTerm_unrestricted
