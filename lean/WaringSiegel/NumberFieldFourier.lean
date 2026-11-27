import WaringSiegel.LatticeFourier
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Literal number-field specialization of coefficient extraction

The frequency map is the actual integral-basis coordinate equivalence of
`𝓞 K`.  Its injectivity is proved by mathlib, not assumed here.

The torus is expressed in integral-basis coordinates.  Identifying those
coordinates with the Minkowski-space quotient by the inverse different is
a further geometric step, unnecessary for this exact counting identity.
-/

noncomputable section

open MeasureTheory
open scoped NumberField BigOperators

namespace WaringSiegel

variable (K : Type*) [Field K] [NumberField K]

abbrev NumberFieldCoordinateIndex := Module.Free.ChooseBasisIndex ℤ (𝓞 K)

/-- The integral coordinate map of the actual ring of integers. -/
def integerCoordinates : (𝓞 K) →+ (NumberFieldCoordinateIndex K → ℤ) :=
  (NumberField.RingOfIntegers.basis K).equivFun.toLinearMap.toAddMonoidHom

theorem integerCoordinates_injective : Function.Injective (integerCoordinates K) :=
  (NumberField.RingOfIntegers.basis K).equivFun.injective

/-- The Fourier integral is the literal weighted count of algebraic-integer
tuples satisfying the power equation. -/
theorem numberField_integral_power_representation_count
    [DecidableEq (𝓞 K)]
    (k s : ℕ) (S : Finset (Fin s → 𝓞 K)) (w : (Fin s → 𝓞 K) → ℂ) (ν : 𝓞 K) :
    (∫ θ, ∑ x ∈ S,
        w x * latticeCharacter
          (integerCoordinates K (∑ i, x i ^ k) - integerCoordinates K ν) θ
        ∂latticeHaar) =
      ∑ x ∈ S, if (∑ i, x i ^ k) = ν then w x else 0 := by
  exact integral_power_representation_count (integerCoordinates K)
    (integerCoordinates_injective K) k s S w ν

/-- Nonvanishing of the coordinate-torus integral supplies an actual tuple of
algebraic integers with the requested sum of powers. -/
theorem numberField_power_representation_of_integral_ne_zero
    (k s : ℕ) (S : Finset (Fin s → 𝓞 K)) (w : (Fin s → 𝓞 K) → ℂ) (ν : 𝓞 K)
    (h : (∫ θ, ∑ x ∈ S,
      w x * latticeCharacter
        (integerCoordinates K (∑ i, x i ^ k) - integerCoordinates K ν) θ
      ∂latticeHaar) ≠ 0) :
    ∃ x ∈ S, (∑ i, x i ^ k) = ν := by
  exact power_representation_of_integral_ne_zero (integerCoordinates K)
    (integerCoordinates_injective K) k s S w ν h

end WaringSiegel
