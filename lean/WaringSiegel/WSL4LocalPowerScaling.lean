import WaringSiegel.WSL2LocalScaling
import WaringSiegel.WSL3MomentLocalPowerPrimitiveAll

/-! # Exact precision fibers for power congruences of every degree

Generalizes the checked cubic quotient-fiber argument without changing the
actual quotient rings, tuples, or counts.
-/
noncomputable section
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : ℕ)

def PowerCongruenceTuples (R : Type*) [CommRing R] [IsLocalRing R]
    (n r s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ maximalIdeal R ^ (n + r) //
    (∑ i, (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_add_right n r)) (x i)) ^ k) =
        Ideal.Quotient.mk (maximalIdeal R ^ n) a}

instance powerCongruenceTuples_finite [Finite (ResidueField R)]
    (n r s : ℕ) (a : R) : Finite (PowerCongruenceTuples k R n r s a) := by
  letI := dvr_power_quotient_finite (R := R) (n + r)
  unfold PowerCongruenceTuples
  infer_instance

def powerCongruenceTuplesEquiv (n r s : ℕ) (a : R) :
    PowerCongruenceTuples k R n r s a ≃
      (Σ b : LocalPowerSolutions R (maximalIdeal R ^ n) k s a,
        ∀ i : Fin s, {x : R ⧸ maximalIdeal R ^ (n + r) //
          Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n r)) x = b.val i}) where
  toFun x := ⟨⟨fun i => Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_add_right n r)) (x.val i), x.property⟩,
      fun i => ⟨x.val i, rfl⟩⟩
  invFun x := ⟨fun i => (x.2 i).val, by
    simpa only [(x.2 _).property] using x.1.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨b, hb⟩, x⟩
    have he : (fun i => Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_add_right n r)) (x i).val) = b :=
      funext (fun i => (x i).property)
    apply Sigma.ext (Subtype.ext he)
    apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    apply (Subtype.heq_iff_coe_eq (fun z => by dsimp; rw [(x i).property])).mpr
    rfl

/-- Requiring a congruence at a lower precision leaves `r` free digits in
all `s` coordinates. -/
theorem power_congruence_tuples_card [Finite (ResidueField R)]
    (n r s : ℕ) (a : R) :
    Nat.card (PowerCongruenceTuples k R n r s a) =
      localPowerSolutionCount R (maximalIdeal R ^ n) k s a *
        Nat.card (ResidueField R) ^ (s * r) := by
  classical
  letI := dvr_power_quotient_finite (R := R) n
  letI := dvr_power_quotient_finite (R := R) (n + r)
  letI := Fintype.ofFinite (LocalPowerSolutions R (maximalIdeal R ^ n) k s a)
  rw [Nat.card_congr (powerCongruenceTuplesEquiv k n r s a), Nat.card_sigma]
  simp only [Nat.card_pi, dvr_reduction_fiber_card, Finset.prod_const,
    Finset.card_univ, Nat.card_fin, ← pow_mul, Nat.mul_comm r s,
    Finset.sum_const, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    localPowerSolutionCount, Nat.cast_id]

#print axioms power_congruence_tuples_card
end WaringSiegel.WSL4Local
