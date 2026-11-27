import Waring.RationalHeight
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Defs

/-!
# Attainment and the denominator-error product

Bounded intrinsic-cost sets contain only finitely many reduced fractions.
Consequently the infimum defining height is an attained minimum. Dirichlet's
bound then shows that its minimizing denominator-error product is at most one.
-/

noncomputable section

namespace Waring.RationalHeight

theorem numerator_bound {V α C : ℝ} (hV : 0 < V) {r : ℚ}
    (hr : cost V α r ≤ C) : |(r.num : ℝ)| ≤ C * |α| + C / V := by
  have hd : (r.den : ℝ) ≤ C := (le_max_left _ _).trans hr
  have he : |(r.den : ℝ) * α - (r.num : ℝ)| ≤ C / V := by
    apply (le_div_iff₀ hV).mpr
    have H := (le_max_right _ _).trans hr
    simpa only [mul_comm] using H
  calc
    |(r.num : ℝ)| = |(r.den : ℝ) * α - ((r.den : ℝ) * α - (r.num : ℝ))| := by ring_nf
    _ ≤ |(r.den : ℝ) * α| + |(r.den : ℝ) * α - (r.num : ℝ)| := abs_sub _ _
    _ ≤ C * |α| + C / V := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r.den)]
      exact add_le_add (mul_le_mul_of_nonneg_right hd (abs_nonneg α)) he

theorem finite_cost_sublevel {V : ℝ} (hV : 0 < V) (α C : ℝ) :
    {r : ℚ | cost V α r ≤ C}.Finite := by
  let D : ℕ := ⌈C⌉₊
  let B : ℕ := ⌈C * |α| + C / V⌉₊
  have hfin : ((Set.Icc (-(B : ℤ)) (B : ℤ)) ×ˢ (Set.Icc (0 : ℕ) D)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hinj : Function.Injective (fun r : ℚ => (r.num, r.den)) := by
    intro r s h
    exact Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  apply (hfin.preimage hinj.injOn).subset
  intro r hr
  have hd : (r.den : ℝ) ≤ (D : ℝ) :=
    ((le_max_left _ _).trans hr).trans (Nat.le_ceil C)
  have hb : |(r.num : ℝ)| ≤ (B : ℝ) :=
    (numerator_bound hV hr).trans (Nat.le_ceil _)
  have hbZ : |r.num| ≤ (B : ℤ) := by exact_mod_cast hb
  exact ⟨abs_le.mp hbZ, ⟨Nat.zero_le _, by exact_mod_cast hd⟩⟩

theorem exists_minimizer {V : ℝ} (hV : 0 < V) (α : ℝ) :
    ∃ r : ℚ, cost V α r = height V α := by
  let C := cost V α 0
  obtain ⟨r, hr, hmin⟩ := Set.exists_min_image {r : ℚ | cost V α r ≤ C}
    (cost V α) (finite_cost_sublevel hV α C) ⟨0, by change cost V α 0 ≤ C; rfl⟩
  refine ⟨r, le_antisymm ?_ (height_le_cost V α r)⟩
  apply le_csInf (Set.range_nonempty (cost V α))
  rintro _ ⟨s, rfl⟩
  by_cases hs : cost V α s ≤ C
  · exact hmin s hs
  · exact hr.trans (le_of_not_ge hs)

/-- A minimizing maximum-height approximant satisfies the usual good-
approximant condition `q*|q*α-a|≤1`, with no unproved choice assumption. -/
theorem exists_good_minimizer {V : ℝ} (hV : 1 ≤ V) (α : ℝ) :
    ∃ r : ℚ, cost V α r = height V α ∧
      (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1 := by
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  obtain ⟨r, hr⟩ := exists_minimizer hVpos α
  refine ⟨r, hr, ?_⟩
  have hc : cost V α r ≤ Real.sqrt V := hr ▸ height_le_sqrt hV α
  have hd : (r.den : ℝ) ≤ Real.sqrt V := (le_max_left _ _).trans hc
  have he : V * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ Real.sqrt V :=
    (le_max_right _ _).trans hc
  have hs : 0 ≤ Real.sqrt V := Real.sqrt_nonneg V
  have hm := mul_le_mul hd he (mul_nonneg hVpos.le (abs_nonneg _)) hs
  have hs2 : (Real.sqrt V)^2 = V := Real.sq_sqrt hVpos.le
  have hprod : V * ((r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)|) ≤ V := by
    nlinarith [hm]
  exact (mul_le_mul_iff_right₀ hVpos).mp (by simpa using hprod)

def sumCost (V α : ℝ) (r : ℚ) : ℝ :=
  (r.den : ℝ) + V * |(r.den : ℝ) * α - (r.num : ℝ)|

def sumHeight (V α : ℝ) : ℝ := sInf (Set.range (sumCost V α))

theorem max_sum_cost_comparison {V : ℝ} (hV : 0 ≤ V) (α : ℝ) (r : ℚ) :
    cost V α r ≤ sumCost V α r ∧ sumCost V α r ≤ 2 * cost V α r := by
  have hd : (0 : ℝ) ≤ r.den := by positivity
  have he : 0 ≤ V * |(r.den : ℝ) * α - (r.num : ℝ)| := mul_nonneg hV (abs_nonneg _)
  unfold cost sumCost
  constructor
  · exact max_le (le_add_of_nonneg_right he) (le_add_of_nonneg_left hd)
  · have h1 := le_max_left (r.den : ℝ) (V * |(r.den : ℝ) * α - (r.num : ℝ)|)
    have h2 := le_max_right (r.den : ℝ) (V * |(r.den : ℝ) * α - (r.num : ℝ)|)
    linarith

theorem max_sum_height_comparison {V : ℝ} (hV : 0 < V) (α : ℝ) :
    height V α ≤ sumHeight V α ∧ sumHeight V α ≤ 2 * height V α := by
  have hb : BddBelow (Set.range (sumCost V α)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact (one_le_cost V α r).trans (max_sum_cost_comparison hV.le α r).1
  constructor
  · apply le_csInf (Set.range_nonempty (sumCost V α))
    rintro _ ⟨r, rfl⟩
    exact (height_le_cost V α r).trans (max_sum_cost_comparison hV.le α r).1
  · obtain ⟨r, hr⟩ := exists_minimizer hV α
    have hh : sumHeight V α ≤ sumCost V α r := csInf_le hb (Set.mem_range_self r)
    exact hh.trans (hr ▸ (max_sum_cost_comparison hV.le α r).2)

theorem height_mono_conductor {V W α : ℝ} (hW : 0 < W) (hVW : V ≤ W) :
    height V α ≤ height W α := by
  obtain ⟨r, hr⟩ := exists_minimizer hW α
  calc
    height V α ≤ cost V α r := height_le_cost V α r
    _ ≤ cost W α r := max_le_max le_rfl (mul_le_mul_of_nonneg_right hVW (abs_nonneg _))
    _ = height W α := hr

/-- Multiplying the phase by a positive integer changes intrinsic height by
at most that factor. The fraction may become unreduced; reduction is proved
to improve the approximation cost. -/
theorem height_mul_phase_upper {V α : ℝ} (hV : 0 < V) {h : ℕ} (hh : 0 < h) :
    height V ((h : ℝ)*α) ≤ (h : ℝ) * height V α := by
  obtain ⟨r, hr⟩ := exists_minimizer hV α
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hb := height_le_unreduced (α := (h : ℝ)*α) hV.le ((h : ℤ)*r.num) r.pos
  apply hb.trans
  rw [← hr]
  unfold cost
  push_cast
  have heq : (r.den : ℝ) * ((h : ℝ)*α) - (h : ℝ)*(r.num : ℝ) =
      (h : ℝ)*((r.den : ℝ)*α-(r.num : ℝ)) := by ring
  rw [heq, abs_mul, abs_of_pos hhR]
  apply max_le
  · calc
      (r.den : ℝ) ≤ (h : ℝ)*(r.den : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hh1 (show (0:ℝ) ≤ r.den by positivity)
      _ ≤ (h : ℝ)*max (r.den : ℝ) (V*|(r.den : ℝ)*α-(r.num : ℝ)|) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hhR.le
  · calc
      V*((h : ℝ)*|(r.den : ℝ)*α-(r.num : ℝ)|) =
          (h : ℝ)*(V*|(r.den : ℝ)*α-(r.num : ℝ)|) := by ring
      _ ≤ (h : ℝ)*max (r.den : ℝ) (V*|(r.den : ℝ)*α-(r.num : ℝ)|) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hhR.le

theorem height_mul_phase_lower {V α : ℝ} (hV : 0 < V) {h : ℕ} (hh : 0 < h) :
    height V α ≤ (h : ℝ) * height V ((h : ℝ)*α) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hmono : height V α ≤ height ((h : ℝ)*V) α :=
    height_mono_conductor (mul_pos hhR hV) (by nlinarith)
  exact hmono.trans (height_mul_lift hV.le hh le_rfl)

#print axioms exists_good_minimizer
#print axioms max_sum_height_comparison
#print axioms height_mul_phase_upper
#print axioms height_mul_phase_lower

end Waring.RationalHeight
