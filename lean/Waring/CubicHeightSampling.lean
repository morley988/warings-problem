import Waring.CubicExceptionalSampling
import Waring.SampledLinearSecondMoment

/-!
# Refined reciprocal-height sampling along cubes

This is the discrete adaptation of the exceptional-fraction step in the
coefficient sampling argument. The proof chooses actual minimizing fractions,
forces their cross products to agree by an explicit strict cutoff, and sums
the proved cubic divisor-class bound. No sampling theorem is a hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace Waring.CubicHeightSampling
open Waring.RationalHeight Waring.CubicExceptionalSampling

theorem cross_match_of_short_height {U Y α : ℝ} {H h : ℕ} (r s : ℚ)
    (hU : 0 < U) (hY : 0 ≤ Y) (hhH : h ≤ H)
    (hs : cost U (α*(h:ℝ)^3) s ≤ Y)
    (hsmall : (H:ℝ)^3*Y*error α r + (r.den:ℝ)*Y/U < 1) : CrossMatch r s h := by
  have ht : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hsden : (s.den:ℝ) ≤ Y := (le_max_left _ _).trans hs
  have hserr : error (α*(h:ℝ)^3) s ≤ Y/U := by
    apply (le_div_iff₀ hU).mpr
    have h := (le_max_right _ _).trans hs
    simpa only [cost, error, mul_comm] using h
  have hhR : (h:ℝ) ≤ H := by exact_mod_cast hhH
  have hhpow : (h:ℝ)^3 ≤ (H:ℝ)^3 := pow_le_pow_left₀ (by positivity) hhR 3
  have hfirst : (h:ℝ)^3*(s.den:ℝ)*error α r ≤ (H:ℝ)^3*Y*error α r := by
    apply mul_le_mul_of_nonneg_right _ (error_nonneg α r)
    exact mul_le_mul hhpow hsden (by positivity) (by positivity)
  have hsecond : (r.den:ℝ)*error (α*(h:ℝ)^3) s ≤ (r.den:ℝ)*Y/U := by
    have h := mul_le_mul_of_nonneg_left hserr ht.le
    simpa only [mul_div_assoc] using h
  apply SamplingArithmetic.exceptional_rigidity (α := α)
  push_cast
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (h:ℝ)^3*(s.den:ℝ)), abs_of_pos ht]
  have heq : |α*(h:ℝ)^3*(s.den:ℝ)-(s.num:ℝ)| = error (α*(h:ℝ)^3) s := by
    unfold error
    congr 1
    ring
  rw [heq]
  change (h:ℝ)^3*(s.den:ℝ)*error α r + (r.den:ℝ)*error (α*(h:ℝ)^3) s < 1
  linarith

theorem cubic_reciprocal_sum_with_approximant (H : ℕ) (r : ℚ)
    {U Y α : ℝ} (hU : 1 ≤ U) (hY : 0 < Y)
    (hsmall : (H:ℝ)^3*Y*error α r + (r.den:ℝ)*Y/U < 1) :
    (∑ h ∈ Finset.Icc 1 H, 1 / height U (α*(h:ℝ)^3)) ≤
      (H:ℝ)/Y + 8*(r.den.divisors.card:ℝ)*(H:ℝ)^3 /
        sumCost ((H:ℝ)^3*U) α r := by
  classical
  have hUp : 0 < U := zero_lt_one.trans_le hU
  choose s hs using (fun h : ℕ => exists_minimizer hUp (α*(h:ℝ)^3))
  let S : Finset ℕ := (Finset.Icc 1 H).filter (fun h : ℕ => height U (α*(h:ℝ)^3) < Y)
  have hS : S ⊆ Finset.Icc 1 H := Finset.filter_subset _ _
  have hmatch : ∀ h ∈ S, CrossMatch r (s h) h := by
    intro h hh
    rcases Finset.mem_filter.mp hh with ⟨hb, hshort⟩
    apply cross_match_of_short_height r (s h) hUp hY.le (Finset.mem_Icc.mp hb).2 _ hsmall
    rw [hs h]
    exact hshort.le
  have hex := exceptional_reciprocal_sum S H r s (α := α) hUp.le hS hmatch
  have hpt (h : ℕ) :
      1 / height U (α*(h:ℝ)^3) ≤
        (if height U (α*(h:ℝ)^3) < Y then
          2 * (1 / sumCost U (α*(h:ℝ)^3) (s h)) else 0) + 1/Y := by
    have hb := height_pos U (α*(h:ℝ)^3)
    by_cases hh : height U (α*(h:ℝ)^3) < Y
    · rw [if_pos hh]
      have hc := max_sum_cost_comparison hUp.le (α*(h:ℝ)^3) (s h)
      rw [hs h] at hc
      have hcp : 0 < sumCost U (α*(h:ℝ)^3) (s h) := hb.trans_le hc.1
      have hinv : 1 / height U (α*(h:ℝ)^3) ≤ 2 / sumCost U (α*(h:ℝ)^3) (s h) :=
        (div_le_div_iff₀ hb hcp).mpr (by simpa using hc.2)
      have hYinv : 0 ≤ 1/Y := by positivity
      calc
        _ ≤ 2 / sumCost U (α*(h:ℝ)^3) (s h) := hinv
        _ = 2*(1/sumCost U (α*(h:ℝ)^3) (s h)) := by ring
        _ ≤ 2*(1/sumCost U (α*(h:ℝ)^3) (s h))+1/Y := le_add_of_nonneg_right hYinv
    · rw [if_neg hh, zero_add]
      exact one_div_le_one_div_of_le hY (le_of_not_gt hh)
  calc
    (∑ h ∈ Finset.Icc 1 H, 1 / height U (α*(h:ℝ)^3)) ≤
        ∑ h ∈ Finset.Icc 1 H,
          ((if height U (α*(h:ℝ)^3) < Y then
            2 * (1 / sumCost U (α*(h:ℝ)^3) (s h)) else 0) + 1/Y) :=
      Finset.sum_le_sum (fun h _ => hpt h)
    _ = 2*(∑ h ∈ S, 1/sumCost U (α*(h:ℝ)^3) (s h)) + (H:ℝ)/Y := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum]
      simp [S, div_eq_mul_inv]
    _ ≤ 2*(4*(r.den.divisors.card:ℝ)*(H:ℝ)^3 /
        sumCost ((H:ℝ)^3*U) α r) + (H:ℝ)/Y := by linarith
    _ = (H:ℝ)/Y + 8*(r.den.divisors.card:ℝ)*(H:ℝ)^3 /
        sumCost ((H:ℝ)^3*U) α r := by ring

/-- Dirichlet's upper bound supplies a uniform sufficient cutoff. This is
the `sqrt(JN/H^3)` cutoff in the adapted sampling estimate. -/
theorem cubic_reciprocal_sum (H : ℕ) {U Y α : ℝ} (hH : 0 < H)
    (hU : 1 ≤ U) (hY : 0 < Y)
    (hsize : 2*Y*Real.sqrt ((H:ℝ)^3*U)/U < 1) :
    ∃ r : ℚ, cost ((H:ℝ)^3*U) α r = height ((H:ℝ)^3*U) α ∧
      (∑ h ∈ Finset.Icc 1 H, 1 / height U (α*(h:ℝ)^3)) ≤
        (H:ℝ)/Y + 8*(r.den.divisors.card:ℝ)*(H:ℝ)^3 /
          height ((H:ℝ)^3*U) α := by
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0:ℝ) < H := zero_lt_one.trans_le hHR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hH3 : (1:ℝ) ≤ (H:ℝ)^3 := one_le_pow₀ hHR
  have hV : 1 ≤ (H:ℝ)^3*U := one_le_mul_of_one_le_of_one_le hH3 hU
  have hVp : 0 < (H:ℝ)^3*U := zero_lt_one.trans_le hV
  obtain ⟨r, hr⟩ := exists_minimizer hVp α
  have hcost : cost ((H:ℝ)^3*U) α r ≤ Real.sqrt ((H:ℝ)^3*U) := hr ▸ height_le_sqrt hV α
  have ht : (r.den:ℝ) ≤ Real.sqrt ((H:ℝ)^3*U) := (le_max_left _ _).trans hcost
  have he : error α r ≤ Real.sqrt ((H:ℝ)^3*U)/((H:ℝ)^3*U) := by
    apply (le_div_iff₀ hVp).mpr
    have hh := (le_max_right _ _).trans hcost
    simpa only [cost, error, mul_comm] using hh
  have hfirst : (H:ℝ)^3*Y*error α r ≤ Y*Real.sqrt ((H:ℝ)^3*U)/U := by
    calc
      _ ≤ (H:ℝ)^3*Y*(Real.sqrt ((H:ℝ)^3*U)/((H:ℝ)^3*U)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by field_simp
  have hsecond : (r.den:ℝ)*Y/U ≤ Y*Real.sqrt ((H:ℝ)^3*U)/U := by
    exact div_le_div_of_nonneg_right (by nlinarith) hUp.le
  have hsmall : (H:ℝ)^3*Y*error α r+(r.den:ℝ)*Y/U < 1 := by
    have hh : Y*Real.sqrt ((H:ℝ)^3*U)/U + Y*Real.sqrt ((H:ℝ)^3*U)/U =
        2*Y*Real.sqrt ((H:ℝ)^3*U)/U := by ring
    linarith
  have hrecip := cubic_reciprocal_sum_with_approximant H r hU hY hsmall
  have hcompare := max_sum_cost_comparison hVp.le α r
  rw [hr] at hcompare
  have hmono : 8*(r.den.divisors.card:ℝ)*(H:ℝ)^3 / sumCost ((H:ℝ)^3*U) α r ≤
      8*(r.den.divisors.card:ℝ)*(H:ℝ)^3 / height ((H:ℝ)^3*U) α :=
    div_le_div_of_nonneg_left (by positivity) (height_pos _ _) hcompare.1
  exact ⟨r, hr, hrecip.trans (add_le_add_left hmono _)⟩

#print axioms cubic_reciprocal_sum

end Waring.CubicHeightSampling
