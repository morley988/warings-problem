import WaringSiegel.WSL3MomentFiniteMean

/-!
# Weighted finite moments and nonnegative power-sum energies

These are exact finite Fourier identities and monotonicity statements.
They supply the coefficient-sensitive bridge from the native integer source
to the number-field Haar moment.
-/

noncomputable section
open Finset GafniTao MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {α : Type*} [Fintype α]

theorem weighted_monomial_grid_mean (q k s : ℕ) [NeZero q]
    (nodes : α → ZMod q) (w : α → ℂ) :
    ((q ^ k : ℕ) : ℝ)⁻¹ *
      ∑ a : Fin k → ZMod q,
        ‖∑ x : α, w x * ZMod.stdAddChar
          (∑ j : Fin k, a j * nodes x ^ (j.val + 1))‖ ^ (2 * s) =
      ∑ xy : (Fin s → α) × (Fin s → α),
        if VinogradovEquations k s nodes xy.1 xy.2 then
          ((∏ i, w (xy.1 i)) * conj (∏ i, w (xy.2 i))).re else 0 := by
  let value : α → Fin k → ZMod q := fun x j => nodes x ^ (j.val + 1)
  let disp := wooleyTupleDisplacement q k s value
  have hdisp (xy : (Fin s → α) × (Fin s → α)) :
      disp xy = 0 ↔ VinogradovEquations k s nodes xy.1 xy.2 := by
    simp only [disp, wooleyTupleDisplacement, value, funext_iff,
      Pi.zero_apply, sub_eq_zero, VinogradovEquations]
  have hphase (a : Fin k → ZMod q) (x : α) :
      ZMod.stdAddChar (∑ j : Fin k, a j * nodes x ^ (j.val + 1)) =
        wooleyPointCharacter q k value a x :=
    wooley_addChar_sum_eq_prod ZMod.stdAddChar _
  have hexpand (a : Fin k → ZMod q) :
      ((‖∑ x : α, w x * ZMod.stdAddChar
          (∑ j : Fin k, a j * nodes x ^ (j.val + 1))‖ ^ (2 * s) : ℝ) : ℂ) =
        ∑ xy : (Fin s → α) × (Fin s → α),
          wooleyTupleCoefficient s w xy * ∏ j, ZMod.stdAddChar (a j * disp xy j) := by
    simp_rw [hphase]
    rw [Complex.ofReal_pow, ← ford_pow_mul_conj_pow,
      wooley_weighted_sum_abs_pow_expand]
    simp only [wooley_tuple_pair_character, disp]
  have hcomplex :
      (((q ^ k : ℕ) : ℂ)⁻¹) *
        ∑ a : Fin k → ZMod q,
          ((‖∑ x : α, w x * ZMod.stdAddChar
            (∑ j : Fin k, a j * nodes x ^ (j.val + 1))‖ ^ (2 * s) : ℝ) : ℂ) =
        ∑ xy : (Fin s → α) × (Fin s → α),
          if VinogradovEquations k s nodes xy.1 xy.2 then
            wooleyTupleCoefficient s w xy else 0 := by
    simp_rw [hexpand]
    rw [wooley_weighted_grid_average_eq_filter]
    simp only [hdisp]
  have h := congrArg Complex.re hcomplex
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.re_sum, apply_ite Complex.re, Complex.zero_re,
    wooleyTupleCoefficient] using h

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A literal weighted power-sum solution energy.  Nonnegative weights make
it monotone under ring reduction. -/
def weightedVinogradovEnergy (k s : ℕ) (nodes : α → R) (w : α → ℝ) : ℝ :=
  ∑ xy : (Fin s → α) × (Fin s → α),
    if VinogradovEquations k s nodes xy.1 xy.2 then
      (∏ i, w (xy.1 i)) * ∏ i, w (xy.2 i) else 0

theorem weightedVinogradovEnergy_nonneg (k s : ℕ) (nodes : α → R)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ weightedVinogradovEnergy k s nodes w := by
  apply Finset.sum_nonneg
  intro xy hxy
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw _))
      (Finset.prod_nonneg (fun i _ => hw _))
  · rfl

theorem weightedVinogradovEnergy_mul (k s : ℕ) (nodes : α → R)
    (w : α → ℝ) (c : ℝ) :
    weightedVinogradovEnergy k s nodes (fun x => c * w x) =
      c ^ (2 * s) * weightedVinogradovEnergy k s nodes w := by
  unfold weightedVinogradovEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  split_ifs
  · simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [pow_mul, pow_two]
    ring
  · simp

theorem weightedVinogradovEnergy_le_map (f : R →+* S) (k s : ℕ)
    (nodes : α → R) (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    weightedVinogradovEnergy k s nodes w ≤
      weightedVinogradovEnergy k s (fun x => f (nodes x)) w := by
  apply Finset.sum_le_sum
  intro xy hxy
  by_cases h : VinogradovEquations k s nodes xy.1 xy.2
  · have hm : VinogradovEquations k s (fun x => f (nodes x)) xy.1 xy.2 := by
      intro j
      simpa only [map_sum, map_pow] using congrArg f (h j)
    rw [if_pos h, if_pos hm]
  · rw [if_neg h]
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw _))
        (Finset.prod_nonneg (fun i _ => hw _))
    · rfl

theorem real_weighted_monomial_grid_mean (q k s : ℕ) [NeZero q]
    (nodes : α → ZMod q) (w : α → ℝ) :
    ((q ^ k : ℕ) : ℝ)⁻¹ *
      ∑ a : Fin k → ZMod q,
        ‖∑ x : α, (w x : ℂ) * ZMod.stdAddChar
          (∑ j : Fin k, a j * nodes x ^ (j.val + 1))‖ ^ (2 * s) =
      weightedVinogradovEnergy k s nodes w := by
  rw [weighted_monomial_grid_mean]
  simp only [weightedVinogradovEnergy, ← Complex.ofReal_prod,
    Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem vinogradov_moment_le_norm_weighted_energy
    {ι : Type*} [Fintype ι] (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (k s : ℕ) (nodes : α → R) (w : α → ℂ) :
    (∫ θ, ‖frequencySum (vinogradovFrequency coord k nodes) w θ‖ ^ (2 * s) ∂latticeHaar) ≤
      weightedVinogradovEnergy k s nodes (fun x => ‖w x‖) := by
  rw [integral_vinogradov_weighted coord hcoord]
  apply Finset.sum_le_sum
  intro xy hxy
  split_ifs
  · calc
      _ ≤ ‖(∏ i, w (xy.1 i)) * conj (∏ i, w (xy.2 i))‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, Complex.norm_conj, norm_prod, norm_prod]
  · rfl

#print axioms weighted_monomial_grid_mean
#print axioms vinogradov_moment_le_norm_weighted_energy

end WaringSiegel.WSL3
