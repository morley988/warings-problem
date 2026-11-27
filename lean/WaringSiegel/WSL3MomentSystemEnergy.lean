import WaringSiegel.WSL3MomentWeightedSource
import Mathlib.Algebra.Order.Chebyshev

/-!
# Exact weighted energies for arbitrary finite systems

This module generalizes the monomial identities to arbitrary value maps.
It supplies the literal equation and finite Fourier interfaces needed to
normalize a sparse polynomial system on a small p-adic residue class.
-/

noncomputable section
open Finset GafniTao MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {α A B : Type*} [Fintype α] [AddCommMonoid A] [AddCommMonoid B]

def weightedSystemEnergy (s : ℕ) (value : α → A) (w : α → ℝ) : ℝ :=
  ∑ xy : (Fin s → α) × (Fin s → α),
    if (∑ i, value (xy.1 i)) = (∑ i, value (xy.2 i)) then
      (∏ i, w (xy.1 i)) * ∏ i, w (xy.2 i) else 0

theorem weightedSystemEnergy_nonneg (s : ℕ) (value : α → A)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ weightedSystemEnergy s value w := by
  apply Finset.sum_nonneg
  intro xy hxy
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw _))
      (Finset.prod_nonneg (fun i _ => hw _))
  · rfl

theorem weightedSystemEnergy_mul (s : ℕ) (value : α → A) (w : α → ℝ) (c : ℝ) :
    weightedSystemEnergy s value (fun x => c*w x) = c^(2*s)*weightedSystemEnergy s value w := by
  unfold weightedSystemEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  split_ifs
  · simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul, pow_two]
    ring
  · simp

theorem weightedSystemEnergy_le_of_equations (s : ℕ) (value : α → A) (value' : α → B)
    (heq : ∀ x y : Fin s → α, (∑ i, value (x i)) = (∑ i, value (y i)) →
      (∑ i, value' (x i)) = (∑ i, value' (y i)))
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    weightedSystemEnergy s value w ≤ weightedSystemEnergy s value' w := by
  apply Finset.sum_le_sum
  intro xy hxy
  by_cases h : (∑ i, value (xy.1 i)) = (∑ i, value (xy.2 i))
  · rw [if_pos h, if_pos (heq xy.1 xy.2 h)]
  · rw [if_neg h]
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw _))
        (Finset.prod_nonneg (fun i _ => hw _))
    · rfl

theorem weightedSystemEnergy_le_map (f : A →+ B) (s : ℕ) (value : α → A)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    weightedSystemEnergy s value w ≤ weightedSystemEnergy s (fun x => f (value x)) w :=
  weightedSystemEnergy_le_of_equations s value _ (fun x y h => by
    simpa only [map_sum] using congrArg f h) w hw

/-- Exact finite-grid Fourier identity for an arbitrary system of values. -/
theorem weighted_system_grid_mean (q r s : ℕ) [NeZero q]
    (value : α → Fin r → ZMod q) (w : α → ℝ) :
    ((q^r : ℕ) : ℝ)⁻¹ * ∑ a : Fin r → ZMod q,
      ‖∑ x, (w x : ℂ)*ZMod.stdAddChar (∑ j, a j*value x j)‖^(2*s) =
      weightedSystemEnergy s value w := by
  classical
  let disp := wooleyTupleDisplacement q r s value
  have hdisp (xy : (Fin s → α) × (Fin s → α)) :
      disp xy = 0 ↔ (∑ i, value (xy.1 i)) = (∑ i, value (xy.2 i)) := by
    simp only [disp, wooleyTupleDisplacement, funext_iff, Pi.zero_apply,
      sub_eq_zero, Finset.sum_apply]
  have hphase (a : Fin r → ZMod q) (x : α) :
      ZMod.stdAddChar (∑ j, a j*value x j) = wooleyPointCharacter q r value a x :=
    wooley_addChar_sum_eq_prod ZMod.stdAddChar _
  have hexpand (a : Fin r → ZMod q) :
      ((‖∑ x, (w x : ℂ)*ZMod.stdAddChar (∑ j, a j*value x j)‖^(2*s) : ℝ) : ℂ) =
        ∑ xy : (Fin s → α) × (Fin s → α),
          wooleyTupleCoefficient s (fun x => (w x : ℂ)) xy *
            ∏ j, ZMod.stdAddChar (a j*disp xy j) := by
    simp_rw [hphase]
    rw [Complex.ofReal_pow, ← ford_pow_mul_conj_pow, wooley_weighted_sum_abs_pow_expand]
    simp only [wooley_tuple_pair_character, disp]
  have hcomplex :
      (((q^r : ℕ) : ℂ)⁻¹) * ∑ a : Fin r → ZMod q,
        ((‖∑ x, (w x : ℂ)*ZMod.stdAddChar (∑ j, a j*value x j)‖^(2*s) : ℝ) : ℂ) =
      ∑ xy : (Fin s → α) × (Fin s → α),
        if (∑ i, value (xy.1 i)) = (∑ i, value (xy.2 i)) then
          wooleyTupleCoefficient s (fun x => (w x : ℂ)) xy else 0 := by
    simp_rw [hexpand]
    rw [wooley_weighted_grid_average_eq_filter]
    simp only [hdisp]
  have h := congrArg Complex.re hcomplex
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.re_sum, apply_ite Complex.re,
    Complex.zero_re, wooleyTupleCoefficient, ← Complex.ofReal_prod, Complex.conj_ofReal,
    weightedSystemEnergy] at h
  refine h.trans ?_
  unfold weightedSystemEnergy
  apply Finset.sum_congr rfl
  intro xy hxy
  split_ifs <;> rfl

/-- Arbitrary systems of algebraic-integer values have literal weighted
Haar moments bounded by their nonnegative coefficient energies. -/
theorem system_moment_le_norm_weighted_energy {R ι : Type*}
    [AddCommGroup R] [Fintype ι] (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (r s : ℕ) (value : α → Fin r → R)
    (w : α → ℂ) :
    (∫ θ, ‖frequencySum (fun x (ji : Fin r × ι) => coord (value x ji.1) ji.2) w θ‖^(2*s)
      ∂latticeHaar) ≤ weightedSystemEnergy s value (fun x => ‖w x‖) := by
  rw [integral_norm_frequencySum_even]
  apply Finset.sum_le_sum
  intro xy hxy
  have heq :
      (∑ i, (fun ji : Fin r × ι => coord (value (xy.1 i) ji.1) ji.2)) =
        (∑ i, (fun ji : Fin r × ι => coord (value (xy.2 i) ji.1) ji.2)) ↔
      (∑ i, value (xy.1 i)) = (∑ i, value (xy.2 i)) := by
    constructor
    · intro h
      funext j
      apply hcoord
      ext i
      simpa only [Finset.sum_apply, map_sum] using congrFun h (j, i)
    · intro h
      funext ji
      have hj := congrFun h ji.1
      have hc := congrArg (fun x => coord x ji.2) hj
      simpa only [Finset.sum_apply, map_sum] using hc
  by_cases h : (∑ i, value (xy.1 i)) = (∑ i, value (xy.2 i))
  · rw [if_pos (heq.mpr h), if_pos h]
    calc
      _ ≤ ‖(∏ i, w (xy.1 i))*conj (∏ i, w (xy.2 i))‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, Complex.norm_conj, norm_prod, norm_prod]
  · rw [if_neg (fun h' => h (heq.mp h')), if_neg h]

#print axioms weighted_system_grid_mean
#print axioms system_moment_le_norm_weighted_energy

end WaringSiegel.WSL3
