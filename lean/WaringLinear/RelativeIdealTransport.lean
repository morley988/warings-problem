import Mathlib.RingTheory.ClassGroup
import Mathlib.Tactic

/-! # Removing an ideal divisor in efficient differencing

The three integral ideals recording the current lattice, the chosen
divisor and the remaining relative ideal need not be principal. A
representative of the product class and a field scalar suffice. The
algebraic identity applies to any choice of this scalar, including a
totally positive, archimedean-balanced choice in a number field.
-/

noncomputable section
open scoped nonZeroDivisors
open FractionalIdeal

namespace WaringLinear

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsDedekindDomain R]

/-- The fractional ideal (x) divided by the current lattice. -/
def edRelativeIdeal (x : Kˣ) (L : (Ideal R)⁰) : (FractionalIdeal R⁰ K)ˣ :=
  toPrincipalIdeal R K x / FractionalIdeal.mk0 K L

theorem edRelativeIdeal_div (x a : Kˣ) (L D L' : (Ideal R)⁰)
    (h : toPrincipalIdeal R K a * FractionalIdeal.mk0 K L' =
      FractionalIdeal.mk0 K L * FractionalIdeal.mk0 K D) :
    edRelativeIdeal (x/a) L' = edRelativeIdeal x L / FractionalIdeal.mk0 K D := by
  simp only [edRelativeIdeal, map_div, div_div, h]

private theorem edRelativeIdeal_mem (x : Kˣ) (L J : (Ideal R)⁰)
    (h : edRelativeIdeal x L = FractionalIdeal.mk0 K J) :
    (x : K) ∈ (L : FractionalIdeal R⁰ K) := by
  have heq : toPrincipalIdeal R K x =
      FractionalIdeal.mk0 K J * FractionalIdeal.mk0 K L := div_eq_iff_eq_mul.mp h
  have hspan := congrArg Units.val heq
  simp only [coe_toPrincipalIdeal, Units.val_mul, FractionalIdeal.coe_mk0] at hspan
  apply FractionalIdeal.spanSingleton_le_iff_mem.mp
  rw [hspan]
  calc
    _ ≤ 1 * (L : FractionalIdeal R⁰ K) := by
      gcongr
      exact FractionalIdeal.coeIdeal_le_one
    _ = _ := one_mul _

/-- Extracting a nonprincipal ideal divisor transports the root to the
chosen representative of the new lattice class. Its relative ideal is
exactly the residual integral ideal. -/
theorem edIdealClassDivision (x : Kˣ) (L D L' J : (Ideal R)⁰)
    (hClass : ClassGroup.mk0 L' = ClassGroup.mk0 (L*D))
    (hDiv : edRelativeIdeal x L = FractionalIdeal.mk0 K D * FractionalIdeal.mk0 K J) :
    ∃ a : Kˣ,
      toPrincipalIdeal R K a * FractionalIdeal.mk0 K L' =
        FractionalIdeal.mk0 K L * FractionalIdeal.mk0 K D ∧
      edRelativeIdeal (x/a) L' = FractionalIdeal.mk0 K J ∧
      ((x/a : Kˣ) : K) ∈ (L' : FractionalIdeal R⁰ K) := by
  obtain ⟨b, hb, h⟩ := (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mp hClass
  let a := Units.mk0 b hb
  have hscale : toPrincipalIdeal R K a * FractionalIdeal.mk0 K L' =
      FractionalIdeal.mk0 K L * FractionalIdeal.mk0 K D := by
    rw [← map_mul]
    apply Units.ext
    simpa only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, a,
      Units.val_mk0] using h
  have hrem : edRelativeIdeal (x/a) L' = FractionalIdeal.mk0 K J := by
    rw [edRelativeIdeal_div x a L D L' hscale, hDiv, mul_comm, mul_div_cancel_right]
  exact ⟨a, hscale, hrem, edRelativeIdeal_mem (x/a) L' J hrem⟩

#print axioms edRelativeIdeal_div
#print axioms edIdealClassDivision

end WaringLinear
