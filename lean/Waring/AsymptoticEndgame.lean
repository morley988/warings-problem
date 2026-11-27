import Waring.Representation
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Strict power savings and the eventual representation conclusion

The generic circle-method endgame below uses the actual finite count from
`Representation.lean`. Its missing premises are explicit estimates for a
decomposition of that count; the Waring conclusion is not a premise.
-/

open Filter Asymptotics
open scoped Topology

namespace Waring.AsymptoticEndgame

theorem rpow_isLittleO_rpow {a b : ℝ} (hab : a < b) :
    (fun x : ℝ => x ^ a) =o[atTop] (fun x : ℝ => x ^ b) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
  · have heq : (fun x : ℝ => x ^ a / x ^ b) =ᶠ[atTop]
        (fun x : ℝ => x ^ (-(b-a))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_sub hx]
      congr 1
      ring
    rw [tendsto_congr' heq]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hz
    exact False.elim ((Real.rpow_pos_of_pos hx b).ne' hz)

/-- Any strict power saving is little-o of the main scale, including along
the nonintegral lengths `P = n^(1/k)` used by the circle method. -/
theorem power_saving_isLittleO {ι : Type*} {l : Filter ι}
    {P f : ι → ℝ} {main saving : ℝ} (hsaving : 0 < saving)
    (hP : Tendsto P l atTop)
    (hbound : f =O[l] (fun x => P x ^ (main-saving))) :
    f =o[l] (fun x => P x ^ main) := by
  exact hbound.trans_isLittleO
    ((rpow_isLittleO_rpow (sub_lt_self main hsaving)).comp_tendsto hP)

/-- A positive main term and a little-o total error imply the actual Waring bound. -/
theorem waringBound_of_main_and_small_error {k s : ℕ}
    {main error scale : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hdecomp : ∀ᶠ n in atTop,
      (representationCount k s n : ℝ) = main n + error n)
    (hmain : ∀ᶠ n in atTop, c * scale n ≤ main n)
    (herror : error =o[atTop] scale) : WaringBound k s := by
  have he := herror.def (half_pos hc)
  have hpos : ∀ᶠ n in atTop, 0 < representationCount k s n := by
    filter_upwards [hscale, hdecomp, hmain, he] with n hs hd hm herr
    have hb : |error n| ≤ c * scale n / 2 := by
      simpa only [Real.norm_eq_abs, abs_of_pos hs, div_mul_eq_mul_div] using herr
    exact count_pos_of_major_minor hc hs hd hm hb
  exact waringBound_of_eventually_count_pos (eventually_atTop.mp hpos)

/-- Separate major-arc pruning and minor-arc errors can be combined without
altering the positive main term. -/
theorem waringBound_of_two_small_errors {k s : ℕ}
    {main pruning minor scale : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hdecomp : ∀ᶠ n in atTop,
      (representationCount k s n : ℝ) = main n + (pruning n + minor n))
    (hmain : ∀ᶠ n in atTop, c * scale n ≤ main n)
    (hpruning : pruning =o[atTop] scale)
    (hminor : minor =o[atTop] scale) : WaringBound k s := by
  exact waringBound_of_main_and_small_error hc hscale hdecomp hmain (hpruning.add hminor)

end Waring.AsymptoticEndgame
