import WaringSiegel.WSL3UnitFirstDerivative

/-!
# Real cubic stationary cancellation on a positive source interval

The phase derivative is monotone. We cut at its levels -delta and delta,
apply first-derivative cancellation on the two outer intervals, and control
the middle interval by its length. Optimizing delta proves square-root
cancellation uniformly in the arbitrary linear twist.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

/-- A continuous monotone function can be cut at an arbitrary level, with
empty outer intervals allowed. -/
theorem exists_monotone_level_cut {a b : ℝ} (hab : a ≤ b) {D : ℝ → ℝ}
    (hD : ContinuousOn D (Set.Icc a b)) (hmono : MonotoneOn D (Set.Icc a b)) (q : ℝ) :
    ∃ c ∈ Set.Icc a b,
      (a < c → ∀ x ∈ Set.Icc a c, D x ≤ q) ∧
      (c < b → ∀ x ∈ Set.Icc c b, q ≤ D x) := by
  by_cases hqa : q ≤ D a
  · refine ⟨a,⟨le_rfl,hab⟩,fun h => (lt_irrefl a h).elim,fun _ x hx => ?_⟩
    exact hqa.trans (hmono ⟨le_rfl,hab⟩ hx hx.1)
  by_cases hbq : D b ≤ q
  · refine ⟨b,⟨hab,le_rfl⟩,fun _ x hx => ?_,fun h => (lt_irrefl b h).elim⟩
    exact (hmono hx ⟨hab,le_rfl⟩ hx.2).trans hbq
  obtain ⟨c,hc,hcq⟩ := intermediate_value_Icc hab hD
    ⟨(lt_of_not_ge hqa).le,(lt_of_not_ge hbq).le⟩
  refine ⟨c,hc,fun _ x hx => ?_,fun _ x hx => ?_⟩
  · rw [← hcq]
    exact hmono ⟨hx.1,hx.2.trans hc.2⟩ hc hx.2
  · rw [← hcq]
    exact hmono hc ⟨hc.1.trans hx.1,hx.2⟩ hx.1

/-- Genuine square-root cancellation for a cubic phase on a positive
interval, uniformly in the real linear coefficient. -/
theorem real_cubic_stationary_interval_bound {a b theta : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (htheta : 0 < theta) (u : ℝ) :
    ‖∫ x in a..b, realCubicPhase theta u x‖ ≤ 9 / Real.sqrt (theta*a) := by
  let delta : ℝ := Real.sqrt (theta*a)
  have hd : 0 < delta := Real.sqrt_pos.mpr (mul_pos htheta ha)
  have hd2 : delta^2 = theta*a := Real.sq_sqrt (mul_pos htheta ha).le
  let D : ℝ → ℝ := fun x => 3*theta*x^2+u
  have hDc : Continuous D := by fun_prop
  have hmono : MonotoneOn D (Set.Icc a b) := by
    intro x hx y hy hxy
    have hp := pow_le_pow_left₀ (ha.le.trans hx.1) hxy 2
    dsimp only [D]
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 3*theta)]
  obtain ⟨c,hc,hcl,hcr⟩ := exists_monotone_level_cut hab hDc.continuousOn hmono (-delta)
  obtain ⟨d,hdm,hdl,hdr⟩ := exists_monotone_level_cut hab hDc.continuousOn hmono delta
  have hcd : c ≤ d := by
    by_contra hn
    have hdc : d < c := lt_of_not_ge hn
    have hca : a < c := hdm.1.trans_lt hdc
    have hdb : d < b := hdc.trans_le hc.2
    have hl := hcl hca c ⟨hc.1,le_rfl⟩
    have hr := hdr hdb d ⟨le_rfl,hdm.2⟩
    have hm := hmono hdm hc hdc.le
    linarith
  have hleft : ‖∫ x in a..c, realCubicPhase theta u x‖ ≤ 4/delta := by
    by_cases he : c = a
    · subst c
      simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · apply real_cubic_first_derivative_bound ha.le hc.1 htheta.le hd
      intro x hx
      have hx' := hcl (lt_of_le_of_ne hc.1 (Ne.symm he)) x hx
      dsimp only [D] at hx'
      linarith [neg_le_abs (3*theta*x^2+u)]
  have hright : ‖∫ x in d..b, realCubicPhase theta u x‖ ≤ 4/delta := by
    by_cases he : d = b
    · subst d
      simp only [intervalIntegral.integral_same, norm_zero]
      positivity
    · apply real_cubic_first_derivative_bound (ha.le.trans hdm.1) hdm.2 htheta.le hd
      intro x hx
      have hx' := hdr (lt_of_le_of_ne hdm.2 he) x hx
      dsimp only [D] at hx'
      exact hx'.trans (le_abs_self _)
  have hlength : d-c ≤ 1/delta := by
    by_cases he : c = d
    · rw [he, sub_self]
      positivity
    have hlt : c < d := lt_of_le_of_ne hcd he
    have hcD := hcr (hlt.trans_le hdm.2) c ⟨le_rfl,hc.2⟩
    have hdD := hdl (hc.1.trans_lt hlt) d ⟨hdm.1,le_rfl⟩
    have hgrowth : 6*theta*a*(d-c) ≤ D d-D c := by
      have hfactor : 0 ≤ (d-c)*(d+c-2*a) := mul_nonneg (sub_nonneg.mpr hcd) (by linarith [hc.1,hdm.1])
      have hscaled := mul_nonneg htheta.le hfactor
      dsimp only [D]
      nlinarith
    have hbound : 6*theta*a*(d-c) ≤ 2*delta := by linarith
    have heq : 6*theta*a*(d-c) = (2*delta)*(3*delta*(d-c)) := by
      calc
        _ = 6*(theta*a)*(d-c) := by ring
        _ = 6*delta^2*(d-c) := by rw [hd2]
        _ = _ := by ring
    rw [heq] at hbound
    have hsmall : 3*delta*(d-c) ≤ 1 :=
      (mul_le_mul_left (by positivity : 0 < 2*delta)).mp (by simpa only [mul_one] using hbound)
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hmiddle : ‖∫ x in c..d, realCubicPhase theta u x‖ ≤ 1/delta := by
    have hm := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d)
      (C := (1:ℝ)) (fun x _ => (realCubicPhase_norm theta u x).le)
    have hm' : ‖∫ x in c..d, realCubicPhase theta u x‖ ≤ d-c := by
      simpa only [one_mul, abs_of_nonneg (sub_nonneg.mpr hcd)] using hm
    exact hm'.trans hlength
  have hf := (realCubicPhase_contDiff theta u).continuous
  have hsplit : (∫ x in a..b, realCubicPhase theta u x) =
      (∫ x in a..c, realCubicPhase theta u x) +
      (∫ x in c..d, realCubicPhase theta u x) +
      (∫ x in d..b, realCubicPhase theta u x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable a c)
      (hf.intervalIntegrable c d), intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable a d) (hf.intervalIntegrable d b)]
  rw [hsplit]
  calc
    _ ≤ (‖∫ x in a..c, realCubicPhase theta u x‖ +
        ‖∫ x in c..d, realCubicPhase theta u x‖) +
        ‖∫ x in d..b, realCubicPhase theta u x‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ 4/delta+1/delta+4/delta := add_le_add (add_le_add hleft hmiddle) hright
    _ = _ := by dsimp only [delta]; ring

#print axioms real_cubic_stationary_interval_bound
end WaringSiegel.WSL3
