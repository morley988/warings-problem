import WaringSiegel.WSL4WeilFiniteExtension
import WaringSiegel.WSL4WeilLFunction
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! # WSL4: every finite-field additive character is a trace character

The representation is proved by finite additive-character orthogonality.  This
adapter lets the elementary trace-polynomial estimate handle every character,
including characters of residue fields of nontrivial residue degree.
-/

noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators

theorem exists_mulShift_eq_of_isPrimitive
    {F : Type*} [Field F] [Fintype F]
    (φ : AddChar F ℂ) (hφ : φ.IsPrimitive) (ψ : AddChar F ℂ) :
    ∃ a : F, φ.mulShift a = ψ := by
  classical
  by_contra h
  push_neg at h
  have hz : (∑ a : F, ∑ x : F, φ (a * x) * ψ (-x)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hn : φ.mulShift a * ψ⁻¹ ≠ 1 := fun he => h a (mul_inv_eq_one.mp he)
    simpa only [AddChar.mul_apply, AddChar.mulShift_apply, AddChar.inv_apply] using
      AddChar.sum_eq_zero_of_ne_one hn
  have hc : (∑ a : F, ∑ x : F, φ (a * x) * ψ (-x)) = (Fintype.card F : ℂ) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, AddChar.sum_mulShift _ hφ]
    simp
  rw [hc] at hz
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hz

theorem additiveCharacter_trace_ne_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Finite L]
    {ψ : AddChar K ℂ} (hψ : ψ ≠ 1) :
    ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom ≠ 1 := by
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨x, hx⟩ := Algebra.trace_surjective K L a
  apply AddChar.ne_one_iff.mpr
  refine ⟨x, ?_⟩
  change ψ (Algebra.trace K L x) ≠ 1
  rwa [hx]

def fieldTraceAddChar (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] : AddChar F ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom

theorem fieldTraceAddChar_ne_one (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] : fieldTraceAddChar F p ≠ 1 :=
  additiveCharacter_trace_ne_one stdAddChar_ne_one

theorem exists_nonzero_trace_mul_representation
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∃ a : F, a ≠ 0 ∧ ∀ x : F,
      ψ x = ZMod.stdAddChar (Algebra.trace (ZMod p) F (a * x)) := by
  obtain ⟨a, ha⟩ := exists_mulShift_eq_of_isPrimitive (fieldTraceAddChar F p)
    (AddChar.IsPrimitive.of_ne_one (fieldTraceAddChar_ne_one F p)) ψ
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    exact hψ (by simpa only [AddChar.mulShift_zero] using ha.symm)
  · intro x
    rw [← ha]
    rfl

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.exists_mulShift_eq_of_isPrimitive
#print axioms WaringSiegel.WSL4Weil.additiveCharacter_trace_ne_one
#print axioms WaringSiegel.WSL4Weil.exists_nonzero_trace_mul_representation
