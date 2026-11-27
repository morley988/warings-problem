import WaringSiegel.WSL3LocalRestrictedFourier
import WaringSiegel.WSL3LocalConductorShell

/-! # WSL3: unit cubic sums vanish above residue conductor -/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing
open scoped BigOperators Classical NumberField
namespace WaringSiegel

theorem finite_pullback_character_sum_eq_zero
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A]
    (f : A →+ B) (g : B → ℂ) (ψ : AddChar A ℂ)
    (a : A) (ha : f a = 0) (hψ : ψ a ≠ 1) :
    (∑ x : A, g (f x) * ψ x) = 0 := by
  have he := (Equiv.addRight a).bijective.sum_comp (fun x : A => g (f x) * ψ x)
  simp only [Equiv.coe_addRight, map_add, ha, add_zero, ψ.map_add_eq_mul,
    ← mul_assoc, ← Finset.sum_mul] at he
  have hz : (∑ x : A, g (f x) * ψ x) * (ψ a - 1) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hψ)

def UnitCubicRootFiber (R : Type*) [CommRing R] (b : R) :=
  {x : Rˣ // (x : R)^3 = b}

theorem finiteRingUnitPowerSum_three_fibers
    {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) :
    finiteRingUnitPowerSum ψ 3 =
      ∑ b : R, (Nat.card (UnitCubicRootFiber R b) : ℂ) * ψ b := by
  have he := Fintype.sum_fiberwise' (fun x : Rˣ => (x : R)^3) (fun b => ψ b)
  simpa only [finiteRingUnitPowerSum, UnitCubicRootFiber, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card] using he.symm

variable {R : Type*} [CommRing R] [IsLocalRing R]

def unitCubicRootFiberEquivAllUnit (I : Ideal R) (hI : I ≤ maximalIdeal R) (a : R) :
    UnitCubicRootFiber (R ⧸ I) (Ideal.Quotient.mk I a) ≃
      AllUnitLocalCubicSolutions R I hI 1 a where
  toFun x := ⟨(fun _ => (x.1 : R ⧸ I)), by simpa only [Fin.sum_univ_one] using x.2,
    fun _ => (localResidueReduction_ne_zero_iff_isUnit I hI _).mpr x.1.isUnit⟩
  invFun x := ⟨((localResidueReduction_ne_zero_iff_isUnit I hI (x.1 0)).mp (x.2.2 0)).unit,
    by simpa only [IsUnit.unit_spec, Fin.sum_univ_one] using x.2.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    exact IsUnit.unit_spec _
  right_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ((localResidueReduction_ne_zero_iff_isUnit I hI (x.1 0)).mp (x.2.2 0)).unit_spec

def unitCubicRootFiberEquivResidue (a : R) :
    UnitCubicRootFiber (ResidueField R) (residue R a) ≃ AllUnitCubicResidues R 1 a where
  toFun x := ⟨(fun _ => (x.1 : ResidueField R)), by simpa only [Fin.sum_univ_one] using x.2,
    fun _ => Units.ne_zero _⟩
  invFun x := ⟨Units.mk0 (x.1 0) (x.2.2 0), by simpa only [Fin.sum_univ_one] using x.2.1⟩
  left_inv x := by apply Subtype.ext; apply Units.ext; rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [Finite (ResidueField R)]

theorem unit_cubic_root_fiber_count_eq_residue
    (h3 : IsUnit (3 : R)) (n : ℕ) (b : R ⧸ maximalIdeal R^(n+1)) :
    Nat.card (UnitCubicRootFiber (R ⧸ maximalIdeal R^(n+1)) b) =
      Nat.card (UnitCubicRootFiber (ResidueField R)
        (localResidueReduction (maximalIdeal R^(n+1))
          (Ideal.pow_le_self (Nat.succ_ne_zero n)) b)) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [Nat.card_congr (unitCubicRootFiberEquivAllUnit _ (Ideal.pow_le_self (Nat.succ_ne_zero n)) a),
    all_unit_local_cubic_count_exact h3 0 n a,
    localResidueReduction_mk, Nat.card_congr (unitCubicRootFiberEquivResidue a)]
  simp

/-- This is the actual complete unit cubic sum. Nontriviality on the
residue-kernel is the precise conductor condition, not a cancellation premise. -/
theorem local_unit_cubic_sum_vanishes
    (h3 : IsUnit (3 : R)) (n : ℕ)
    [Fintype (R ⧸ maximalIdeal R^(n+1))]
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+1)) ℂ)
    (hC : ¬maximalIdeal R ≤ quotientCharacterConductor (maximalIdeal R^(n+1)) ψ) :
    finiteRingUnitPowerSum ψ 3 = 0 := by
  have hw : ∃ a : R, a ∈ maximalIdeal R ∧
      ∃ x : R, ψ (Ideal.Quotient.mk (maximalIdeal R^(n+1)) (a*x)) ≠ 1 := by
    by_contra h
    push_neg at h
    apply hC
    intro a ha x
    exact h a ha x
  obtain ⟨a,ha,x,hax⟩ := hw
  let f := localResidueReduction (maximalIdeal R^(n+1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n))
  rw [finiteRingUnitPowerSum_three_fibers]
  simp only [unit_cubic_root_fiber_count_eq_residue h3]
  apply finite_pullback_character_sum_eq_zero f.toAddMonoidHom
    (fun b => (Nat.card (UnitCubicRootFiber (ResidueField R) b) : ℂ)) ψ
    (Ideal.Quotient.mk (maximalIdeal R^(n+1)) (a*x)) _ hax
  change residue R (a*x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((maximalIdeal R).mul_mem_right x ha)

end WaringSiegel
#print axioms WaringSiegel.local_unit_cubic_sum_vanishes
