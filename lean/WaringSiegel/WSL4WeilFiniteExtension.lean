/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors of the upstream finite-extension development: Kenny Lau, Kevin Buzzard.
WSL4 adaptation of Mathlib v4.36.0 FieldTheory/Finite/{GaloisField,Extension}.lean
to Lean 4.24, retaining only the finite-field embedding and extension facts needed here.
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Subsingleton

noncomputable section
namespace WaringSiegel.WSL4Weil
open Polynomial

theorem dvd_iterate_pow_sub_self {R : Type*} [CommRing R] (x : R) (q d : ℕ) :
    x ^ q - x ∣ x ^ (q ^ d) - x := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_mul]
    convert dvd_add (ih.trans (sub_dvd_pow_sub_pow (x ^ (q ^ d)) x q))
      (dvd_refl (x ^ q - x)) using 1 <;> ring

theorem dvd_pow_pow_sub_self_of_dvd {R : Type*} [CommRing R]
    (x : R) (q : ℕ) {m n : ℕ} (h : m ∣ n) :
    x ^ (q ^ m) - x ∣ x ^ (q ^ n) - x := by
  obtain ⟨d, rfl⟩ := h
  simpa only [pow_mul] using dvd_iterate_pow_sub_self x (q ^ m) d

theorem nonempty_algHom_of_finrank_dvd
    {F K L : Type*} [Field F] [Field K] [Algebra F K]
    [Field L] [Algebra F L] [Finite L]
    (h : Module.finrank F K ∣ Module.finrank F L) :
    Nonempty (K →ₐ[F] L) := by
  letI : Finite F := Finite.of_injective _ (algebraMap F L).injective
  letI : Fintype F := Fintype.ofFinite F
  letI : Module.Finite F K := Module.finite_of_finrank_pos
    (Nat.pos_of_dvd_of_pos h Module.finrank_pos)
  letI : Finite K := Module.finite_of_finite F
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype L := Fintype.ofFinite L
  refine ⟨Polynomial.IsSplittingField.lift K (X ^ Fintype.card K - X) ?_⟩
  refine Polynomial.splits_of_splits_of_dvd (algebraMap F L)
    (FiniteField.X_pow_card_sub_X_ne_zero F (Fintype.one_lt_card (α := L))) ?_ ?_
  · simpa only [pow_one] using (FiniteField.isSplittingField_sub L F).splits
  · rw [Module.card_eq_pow_finrank (K := F), Module.card_eq_pow_finrank (K := F) (V := L)]
    exact dvd_pow_pow_sub_self_of_dvd (X : F[X]) (Fintype.card F) h

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [NeZero n]

def Extension : Type :=
  letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

theorem finrank_zmod_extension [A : Algebra (ZMod p) k] :
    Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n := by
  have hA : A = ZMod.algebra k p := Subsingleton.elim _ _
  subst A
  letI := ZMod.algebra k p
  exact GaloisField.finrank p (n := Module.finrank (ZMod p) k * n)
    (mul_ne_zero Module.finrank_pos.ne' (NeZero.ne n))

theorem nonempty_algHom_extension [Algebra (ZMod p) k] :
    Nonempty (k →ₐ[ZMod p] Extension k p n) :=
  nonempty_algHom_of_finrank_dvd
    (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

noncomputable instance extensionAlgebra : Algebra k (Extension k p n) :=
  letI := ZMod.algebra k p
  (nonempty_algHom_extension k p n).some.toAlgebra

instance extensionModuleFinite : Module.Finite k (Extension k p n) := .of_finite

instance extensionScalarTower [Algebra (ZMod p) k] :
    IsScalarTower (ZMod p) k (Extension k p n) :=
  .of_algebraMap_eq' (Subsingleton.elim _ _)

theorem natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n := by
  letI := ZMod.algebra k p
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype (Extension k p n) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p),
    Module.card_eq_pow_finrank (K := ZMod p) (V := k),
    finrank_zmod_extension, pow_mul]

theorem finrank_extension : Module.finrank k (Extension k p n) = n := by
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype (Extension k p n) := Fintype.ofFinite _
  apply Nat.pow_right_injective (Fintype.one_lt_card (α := k))
  change Fintype.card k ^ Module.finrank k (Extension k p n) = Fintype.card k ^ n
  rw [← Module.card_eq_pow_finrank (K := k) (V := Extension k p n), ← Nat.card_eq_fintype_card,
    natCard_extension, Nat.card_eq_fintype_card]

instance extensionIsSplittingField :
    IsSplittingField k (Extension k p n) (X ^ Nat.card k ^ n - X) := by
  letI : Fintype (Extension k p n) := Fintype.ofFinite _
  convert FiniteField.isSplittingField_sub (Extension k p n) k using 1
  rw [← Nat.card_eq_fintype_card, natCard_extension]

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.nonempty_algHom_of_finrank_dvd
#print axioms WaringSiegel.WSL4Weil.natCard_extension
#print axioms WaringSiegel.WSL4Weil.finrank_extension
