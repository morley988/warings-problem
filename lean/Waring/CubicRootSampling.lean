import Waring.CubicRootDivisorClasses
import Waring.CubicHeightSampling

/-!
# Actual reciprocal-height sampling: the cube-root alternative

The same proved exceptional-rational rigidity is composed with the genuine
cube-root divisor-class bound. The logarithmic and divisor factors are explicit.
-/
noncomputable section
open scoped BigOperators
namespace Waring.CubicExceptionalSampling
open Waring.RationalHeight Waring.CubicDivisorClasses

theorem exceptional_reciprocal_cube_root_sum (S : Finset ℕ) (H : ℕ) (r : ℚ) (s : ℕ → ℚ)
    {U α : ℝ} (hH : 0 < H) (hU : 0 ≤ U) (hS : S ⊆ Finset.Icc 1 H)
    (hmatch : ∀ h ∈ S, CrossMatch r (s h) h) :
    (∑ h ∈ S, 1 / sumCost U (α*(h:ℝ)^3) (s h)) ≤
      (r.den.divisors.card : ℝ) * ((H:ℝ) /
        (sumCost ((H:ℝ)^3*U) α r)^(1/3:ℝ)) * (1+Real.log (H:ℝ)) := by
  classical
  let A := U * error α r / (r.den:ℝ)
  have ht : (0:ℝ) < r.den := by exact_mod_cast r.pos
  have hA : 0 ≤ A := by dsimp [A]; exact div_nonneg (mul_nonneg hU (error_nonneg α r)) ht.le
  let weight : ℕ → ℕ → ℝ := fun d h =>
    if d ∣ h^3 then (d:ℝ)/(r.den:ℝ) * (1/(1+A*(h:ℝ)^3)) else 0
  have hw (d h : ℕ) : 0 ≤ weight d h := by dsimp [weight]; split_ifs <;> positivity
  have hsingle (h : ℕ) (hh : h ∈ S) :
      1 / sumCost U (α*(h:ℝ)^3) (s h) ≤ ∑ d ∈ r.den.divisors, weight d h := by
    have hm := hmatch h hh
    have hdmem := class_mem_divisors hm
    have hdcube := (denominator_class hm).2
    have hh := Finset.single_le_sum (fun d _ => hw d h) hdmem
    simpa only [weight, if_pos hdcube, matched_reciprocal hm U α, A] using hh
  have hgroup (d : ℕ) :
      (∑ h ∈ Finset.Icc 1 H, weight d h) = originalClassContribution H d A (r.den:ℝ) := by
    unfold originalClassContribution
    dsimp [weight]
    rw [← Finset.sum_filter, Finset.mul_sum]
  have hden : (r.den:ℝ)+A*(H:ℝ)^3*(r.den:ℝ) = sumCost ((H:ℝ)^3*U) α r := by
    unfold sumCost
    dsimp [A, error]
    field_simp
  calc
    (∑ h ∈ S, 1 / sumCost U (α*(h:ℝ)^3) (s h)) ≤
        ∑ h ∈ S, ∑ d ∈ r.den.divisors, weight d h := Finset.sum_le_sum hsingle
    _ ≤ ∑ h ∈ Finset.Icc 1 H, ∑ d ∈ r.den.divisors, weight d h :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun h _ _ => Finset.sum_nonneg (fun d _ => hw d h))
    _ = ∑ d ∈ r.den.divisors, originalClassContribution H d A (r.den:ℝ) := by
      rw [Finset.sum_comm]
      simp_rw [hgroup]
    _ ≤ ∑ d ∈ r.den.divisors,
        (H:ℝ)/((r.den:ℝ)+A*(H:ℝ)^3*(r.den:ℝ))^(1/3:ℝ)*(1+Real.log (H:ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hdt : (d:ℝ) ≤ r.den := by
        exact_mod_cast Nat.le_of_dvd r.pos (Nat.dvd_of_mem_divisors hd)
      exact originalClassContribution_cube_root hH hdpos hA ht hdt
    _ = (r.den.divisors.card : ℝ) * ((H:ℝ)/(sumCost ((H:ℝ)^3*U) α r)^(1/3:ℝ))*(1+Real.log (H:ℝ)) := by
      rw [hden]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring


end Waring.CubicExceptionalSampling
namespace Waring.CubicHeightSampling
open Waring.RationalHeight Waring.CubicExceptionalSampling

theorem cubic_reciprocal_cube_root_with_approximant (H : ℕ) (r : ℚ)
    {U Y α : ℝ} (hH : 0 < H) (hU : 1 ≤ U) (hY : 0 < Y)
    (hsmall : (H:ℝ)^3*Y*error α r + (r.den:ℝ)*Y/U < 1) :
    (∑ h ∈ Finset.Icc 1 H, 1 / height U (α*(h:ℝ)^3)) ≤
      (H:ℝ)/Y + 2*(r.den.divisors.card:ℝ)*((H:ℝ)/(sumCost ((H:ℝ)^3*U) α r)^(1/3:ℝ))*(1+Real.log (H:ℝ)) := by
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
  have hex := exceptional_reciprocal_cube_root_sum S H r s (α := α) hH hUp.le hS hmatch
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
    _ ≤ 2*((r.den.divisors.card:ℝ)*((H:ℝ)/(sumCost ((H:ℝ)^3*U) α r)^(1/3:ℝ))*(1+Real.log (H:ℝ))) + (H:ℝ)/Y := by linarith
    _ = (H:ℝ)/Y + 2*(r.den.divisors.card:ℝ)*((H:ℝ)/(sumCost ((H:ℝ)^3*U) α r)^(1/3:ℝ))*(1+Real.log (H:ℝ)) := by ring

theorem cubic_reciprocal_cube_root_sum (H : ℕ) {U Y α : ℝ} (hH : 0 < H)
    (hU : 1 ≤ U) (hY : 0 < Y)
    (hsize : 2*Y*Real.sqrt ((H:ℝ)^3*U)/U < 1) :
    ∃ r : ℚ, cost ((H:ℝ)^3*U) α r = height ((H:ℝ)^3*U) α ∧
      (∑ h ∈ Finset.Icc 1 H, 1 / height U (α*(h:ℝ)^3)) ≤
        (H:ℝ)/Y + 2*(r.den.divisors.card:ℝ)*((H:ℝ)/(height ((H:ℝ)^3*U) α)^(1/3:ℝ))*(1+Real.log (H:ℝ)) := by
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
  have hrecip := cubic_reciprocal_cube_root_with_approximant H r hH hU hY hsmall
  have hcompare := max_sum_cost_comparison hVp.le α r
  rw [hr] at hcompare
  have hlog : 0 ≤ 1+Real.log (H:ℝ) := by
    have hh := Real.log_nonneg hHR
    linarith
  have hmono : 2*(r.den.divisors.card:ℝ)*((H:ℝ)/(sumCost ((H:ℝ)^3*U) α r)^(1/3:ℝ))*(1+Real.log (H:ℝ)) ≤
      2*(r.den.divisors.card:ℝ)*((H:ℝ)/(height ((H:ℝ)^3*U) α)^(1/3:ℝ))*(1+Real.log (H:ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hlog
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (height_pos _ _) _)
    exact Real.rpow_le_rpow (height_pos _ _).le hcompare.1 (by norm_num)
  exact ⟨r, hr, hrecip.trans (add_le_add_left hmono _)⟩

#print axioms cubic_reciprocal_cube_root_sum
end Waring.CubicHeightSampling
