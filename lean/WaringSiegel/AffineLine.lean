import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Affine-line rigidity for pairs in a field

This is the algebraic part of the product-arc spacing argument.  In its
number-field application, a norm bound first proves that every displayed
determinant is zero.  That norm bound is not an assumption hidden in this file:
the theorem below states exactly the algebraic implication it proves.
-/

namespace WaringSiegel

variable {F : Type*} [Field F]

/-- Once all differences have zero determinant with one nonvertical difference,
all pairs lie on a common affine line. -/
theorem affine_line_of_determinants
    (S : Set (F × F)) (y₀ a₀ y₁ a₁ : F)
    (hy : y₁ ≠ y₀)
    (hdet : ∀ p ∈ S,
      (p.2 - a₀) * (y₁ - y₀) - (a₁ - a₀) * (p.1 - y₀) = 0) :
    ∃ γ : F, ∀ p ∈ S, p.2 = a₀ + γ * (p.1 - y₀) := by
  refine ⟨(a₁ - a₀) / (y₁ - y₀), ?_⟩
  intro p hp
  have hz : y₁ - y₀ ≠ 0 := sub_ne_zero.mpr hy
  have hmul : (p.2 - a₀) * (y₁ - y₀) = (a₁ - a₀) * (p.1 - y₀) :=
    sub_eq_zero.mp (hdet p hp)
  have hdiv : p.2 - a₀ = (a₁ - a₀) * (p.1 - y₀) / (y₁ - y₀) :=
    (eq_div_iff hz).2 hmul
  calc
    p.2 = a₀ + (p.2 - a₀) := by ring
    _ = a₀ + (a₁ - a₀) * (p.1 - y₀) / (y₁ - y₀) := by rw [hdiv]
    _ = a₀ + ((a₁ - a₀) / (y₁ - y₀)) * (p.1 - y₀) := by ring

/-- The slope supplied by a nonvertical pair is uniquely determined. -/
theorem affine_slope_unique
    (y₀ a₀ y₁ a₁ γ δ : F) (hy : y₁ ≠ y₀)
    (hγ : a₁ = a₀ + γ * (y₁ - y₀))
    (hδ : a₁ = a₀ + δ * (y₁ - y₀)) : γ = δ := by
  have hmul : γ * (y₁ - y₀) = δ * (y₁ - y₀) :=
    add_left_cancel (hγ.symm.trans hδ)
  exact mul_right_cancel₀ (sub_ne_zero.mpr hy) hmul

end WaringSiegel
