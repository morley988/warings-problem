import WaringSiegel.NumberFieldFourier
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Products of actual finite Weyl sums

This extends the recovered classical finite-product expansion to arbitrary
integral-coordinate lattices and algebraic integers. Separate variables may
have separate finite domains and weights, as in the restricted eight-cube
construction. No analytic nonvanishing estimate is assumed by the identity.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NumberField

namespace WaringSiegel
variable {ι : Type*} [Fintype ι]

theorem latticeCharacter_add (m n : ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    latticeCharacter (m+n) θ = latticeCharacter m θ * latticeCharacter n θ := by
  simp only [latticeCharacter, Pi.add_apply, fourier_add, Finset.prod_mul_distrib]

theorem latticeCharacter_zero (θ : ι → AddCircle (1 : ℝ)) :
    latticeCharacter (0 : ι → ℤ) θ = 1 := by
  simp [latticeCharacter]

theorem latticeCharacter_sum {α : Type*} (S : Finset α) (v : α → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    latticeCharacter (∑ a ∈ S, v a) θ = ∏ a ∈ S, latticeCharacter (v a) θ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [latticeCharacter_zero]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, latticeCharacter_add, ih]

def finiteWeylSum {A α : Type*} [CommRing A] [Fintype α]
    (coord : A →+ (ι → ℤ)) (k : ℕ) (nodes : α → A) (w : α → ℂ)
    (θ : ι → AddCircle (1 : ℝ)) : ℂ :=
  ∑ x, w x * latticeCharacter (coord (nodes x ^ k)) θ

/-- Exact product expansion, with independent finite root sets and weights. -/
theorem finiteWeylSum_product_expansion
    {A : Type*} [CommRing A] (coord : A →+ (ι → ℤ)) (k s : ℕ)
    {α : Fin s → Type*} [∀ i, Fintype (α i)]
    (nodes : ∀ i, α i → A) (w : ∀ i, α i → ℂ) (ν : A)
    (θ : ι → AddCircle (1 : ℝ)) :
    (∏ i, finiteWeylSum coord k (nodes i) (w i) θ) *
      latticeCharacter (-coord ν) θ =
    ∑ x : ∀ i, α i, (∏ i, w i (x i)) *
      latticeCharacter (coord (∑ i, nodes i (x i) ^ k) - coord ν) θ := by
  classical
  unfold finiteWeylSum
  rw [Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib, mul_assoc, ← latticeCharacter_sum,
    ← latticeCharacter_add, map_sum]
  rfl

/-- Actual torus integration of the product counts the literal power equation. -/
theorem integral_finiteWeylSum_product
    {A : Type*} [CommRing A] [DecidableEq A]
    (coord : A →+ (ι → ℤ)) (hcoord : Function.Injective coord) (k s : ℕ)
    {α : Fin s → Type*} [∀ i, Fintype (α i)]
    (nodes : ∀ i, α i → A) (w : ∀ i, α i → ℂ) (ν : A) :
    (∫ θ, (∏ i, finiteWeylSum coord k (nodes i) (w i) θ) *
      latticeCharacter (-coord ν) θ ∂latticeHaar) =
    ∑ x : ∀ i, α i, if (∑ i, nodes i (x i) ^ k) = ν then (∏ i, w i (x i)) else 0 := by
  classical
  simp_rw [finiteWeylSum_product_expansion]
  rw [integral_weighted_lattice_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [hcoord.eq_iff]

/-- Specialization to the actual ring of integers with canonical integral coordinates. -/
theorem numberField_integral_Weyl_product
    (K : Type*) [Field K] [NumberField K] [DecidableEq (𝓞 K)] (k s : ℕ)
    {α : Fin s → Type*} [∀ i, Fintype (α i)]
    (nodes : ∀ i, α i → 𝓞 K) (w : ∀ i, α i → ℂ) (ν : 𝓞 K) :
    (∫ θ, (∏ i, finiteWeylSum (integerCoordinates K) k (nodes i) (w i) θ) *
      latticeCharacter (-integerCoordinates K ν) θ ∂latticeHaar) =
    ∑ x : ∀ i, α i, if (∑ i, nodes i (x i) ^ k) = ν then (∏ i, w i (x i)) else 0 :=
  integral_finiteWeylSum_product (integerCoordinates K) (integerCoordinates_injective K)
    k s nodes w ν

end WaringSiegel
