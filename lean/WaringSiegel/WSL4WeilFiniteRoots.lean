/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Adapted in WSL4 from the finite-field polynomial criterion in
Mathlib v4.36.0, FieldTheory/Finite/Extension.lean, for Lean 4.24.
-/
import WaringSiegel.WSL4WeilFiniteExtension

noncomputable section
namespace WaringSiegel.WSL4Weil
open Polynomial

theorem irreducible_natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
    {k : Type*} [Field k] [Finite k] {f : k[X]} (hi : Irreducible f) {n : ℕ} :
    f.natDegree ∣ n ↔ f ∣ X ^ Nat.card k ^ n - X := by
  letI : Fintype k := Fintype.ofFinite k
  constructor
  · intro hdvd
    letI : Fact (Irreducible f) := ⟨hi⟩
    letI : Module.Finite k (AdjoinRoot f) := .of_basis (AdjoinRoot.powerBasis hi.ne_zero).basis
    letI : Finite (AdjoinRoot f) := Module.finite_of_finite k
    letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
    have hc : Nat.card (AdjoinRoot f) = Nat.card k ^ f.natDegree := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Module.card_eq_pow_finrank (K := k),
        (AdjoinRoot.powerBasis hi.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    have hroot : aeval (AdjoinRoot.root f) (X ^ Nat.card k ^ f.natDegree - X : k[X]) = 0 := by
      simp only [map_sub, map_pow, aeval_X]
      rw [← hc, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
    have hbase : f ∣ X ^ Nat.card k ^ f.natDegree - X := by
      exact AdjoinRoot.mk_eq_zero.mp ((AdjoinRoot.aeval_eq _).symm.trans hroot)
    exact hbase.trans (dvd_pow_pow_sub_self_of_dvd (X : k[X]) (Nat.card k) hdvd)
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    letI : NeZero n := ⟨hn⟩
    obtain ⟨p, hp⟩ := CharP.exists k
    letI : CharP k p := hp
    letI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
    let E := Extension k p n
    have hs : Splits (algebraMap k E) f :=
      splits_of_splits_of_dvd (algebraMap k E)
        (FiniteField.X_pow_card_pow_sub_X_ne_zero k hn
          (by simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := k))))
        (IsSplittingField.splits E (X ^ Nat.card k ^ n - X)) h
    obtain ⟨x, hx⟩ := exists_root_of_splits (algebraMap k E) hs hi.degree_pos.ne'
    have hmin : f * C f.leadingCoeff⁻¹ = minpoly k x :=
      minpoly.eq_of_irreducible hi hx
    have hdeg : (minpoly k x).natDegree = f.natDegree := by
      rw [← hmin, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hi.ne_zero))]
    have hd := minpoly.degree_dvd (IsIntegral.of_finite k x)
    rw [hdeg, finrank_extension] at hd
    exact hd

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.irreducible_natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
