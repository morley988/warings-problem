import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Reciprocal integral of a finite height profile

A stage with height `h` and length `l` supplies `min h (l*t/2)` at defect
`t`. Each adjacent pair contributes a constant part and a logarithmic part.
Summing those parts gives the potential used in the linear moment budget.
-/
noncomputable section
namespace WaringEnvelope
open MeasureTheory Set
open scoped BigOperators Interval

private theorem positive_interval_integrable {g : ℝ → ℝ} {x y : ℝ}
    (hg : ContinuousOn g (Ioi 0)) (hx : 0<x) (hy : 0<y) :
    IntervalIntegrable g volume x y := by
  apply ContinuousOn.intervalIntegrable
  exact hg.mono (fun t ht => (lt_min hx hy).trans_le ht.1)

private theorem reciprocal_continuous {V : ℝ → ℝ} (hc : ContinuousOn V (Ioi 0))
    (hp : ∀ t, 0<t → 0<V t) : ContinuousOn (fun t => 1/V t) (Ioi 0) :=
  continuousOn_const.div hc (fun t ht => (hp t ht).ne')

/-- The cost between the two successive points `2h/l` of a height profile. -/
theorem potential_adjacent_band {V : ℝ → ℝ} {H h l L : ℝ}
    (hc : ContinuousOn V (Ioi 0)) (hp : ∀ t, 0<t → 0<V t)
    (hh : 0<h) (hl : 0<l) (hH : h≤H) (hL : l≤L)
    (hupper : ∀ t, 0<t → min H (l*t/2)≤V t)
    (hlower : ∀ t, 0<t → min h (L*t/2)≤V t) :
    (∫ t in (2*h/L)..(2*H/l), 1/V t) ≤ 2/l-2/L+(2/l)*Real.log (H/h) := by
  have hLp : 0<L := hl.trans_le hL
  have hHp : 0<H := hh.trans_le hH
  have ha : 0<2*h/L := by positivity
  have hb : 0<2*h/l := by positivity
  have he : 0<2*H/l := by positivity
  have hab : 2*h/L≤2*h/l := div_le_div_of_nonneg_left (by positivity) hl hL
  have hbe : 2*h/l≤2*H/l := (div_le_div_iff_of_pos_right hl).mpr (by linarith)
  have hg := reciprocal_continuous hc hp
  have hco : (∫ t in (2*h/L)..(2*h/l), 1/V t) ≤ (2*h/l-2*h/L)*(1/h) := by
    calc
      _ ≤ ∫ _t in (2*h/L)..(2*h/l), 1/h := by
        apply intervalIntegral.integral_mono_on hab (positive_interval_integrable hg ha hb) intervalIntegrable_const
        intro t ht
        have hsub : h≤L*t/2 := by nlinarith [(div_le_iff₀ hLp).mp ht.1]
        exact one_div_le_one_div_of_le hh (by simpa [min_eq_left hsub] using hlower t (ha.trans_le ht.1))
      _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]
  have hlin : (∫ t in (2*h/l)..(2*H/l), 1/V t) ≤ (2/l)*Real.log (H/h) := by
    calc
      _ ≤ ∫ t in (2*h/l)..(2*H/l), (2/l)*(1/t) := by
        have hct : ContinuousOn (fun t : ℝ => (2/l)*(1/t)) (Ioi 0) :=
          continuousOn_const.mul (continuousOn_const.div continuousOn_id (fun t ht => (show 0<t from ht).ne'))
        apply intervalIntegral.integral_mono_on hbe (positive_interval_integrable hg hb he)
          (positive_interval_integrable hct hb he)
        intro t ht
        have htpos := hb.trans_le ht.1
        have hsub : l*t/2≤H := by nlinarith [(le_div_iff₀ hl).mp ht.2]
        have hmajor : l*t/2 ≤ V t := by simpa [min_eq_right hsub] using hupper t htpos
        calc
          _ ≤ 1/(l*t/2) := one_div_le_one_div_of_le (by positivity) hmajor
          _ = _ := by field_simp
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos hb he]
        congr 2
        field_simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (positive_interval_integrable hg ha hb)
    (positive_interval_integrable hg hb he)]
  have hpart : (2*h/l-2*h/L)*(1/h) = 2/l-2/L := by field_simp
  rw [hpart] at hco
  linarith

/-- The cost of a decreasing-height, increasing-length menu on an arbitrary
positive continuous potential that majorizes every supplied stage. -/
theorem potential_integral_bound (V : ℝ → ℝ) (h l : ℕ → ℝ) (N : ℕ) (D dstar : ℝ)
    (hc : ContinuousOn V (Ioi 0)) (hp : ∀ t, 0<t → 0<V t)
    (hh : ∀ i≤N, 0<h i) (hl : ∀ i≤N, 0<l i)
    (hdesc : ∀ i<N, h (i+1)≤h i) (lasc : ∀ i<N, l i≤l (i+1))
    (hprofile : ∀ i≤N, ∀ t, 0<t → min (h i) (l i*t/2)≤V t)
    (hstart : 2*h 0/l 0 ≤ D) (hstop : 2*h N/l N ≤ dstar) :
    (∫ t in dstar..D, 1/V t) ≤ D/h 0-2/l N+
       ∑ i ∈ Finset.range N, (2/l i)*Real.log (h i/h (i+1)) := by
  let knee (i : ℕ) := 2*h i/l i
  have hk (i : ℕ) (hi : i≤N) : 0<knee i := div_pos (mul_pos (by norm_num) (hh i hi)) (hl i hi)
  have hD := (hk 0 (Nat.zero_le _)).trans_le hstart
  have hg := reciprocal_continuous hc hp
  have hmenu (j : ℕ) (hj : j≤N) : (∫ t in knee j..D, 1/V t) ≤ D/h 0-2/l j+
       ∑ i ∈ Finset.range j, (2/l i)*Real.log (h i/h (i+1)) := by
    induction j with
    | zero =>
      simp only [Finset.range_zero,Finset.sum_empty,add_zero]
      have h₀ := hh 0 (Nat.zero_le N)
      have l₀ := hl 0 (Nat.zero_le N)
      calc
        _ ≤ ∫ _t in knee 0..D, 1/h 0 := by
          apply intervalIntegral.integral_mono_on hstart (positive_interval_integrable hg (hk 0 hj) hD)
            intervalIntegrable_const
          intro t ht
          have hsub : h 0≤l 0*t/2 := by nlinarith [(div_le_iff₀ l₀).mp ht.1]
          apply one_div_le_one_div_of_le h₀
          simpa [min_eq_left hsub] using hprofile 0 hj t ((hk 0 hj).trans_le ht.1)
        _ = _ := by
          rw [intervalIntegral.integral_const,smul_eq_mul]
          dsimp [knee]
          field_simp
    | succ j ih =>
      have hjn : j<N := hj
      have hprev := ih hjn.le
      have hband := potential_adjacent_band hc hp (hh (j+1) hj) (hl j hjn.le)
        (hdesc j hjn) (lasc j hjn) (hprofile j hjn.le) (hprofile (j+1) hj)
      change (∫ t in knee (j+1)..knee j, 1/V t) ≤ _ at hband
      rw [Finset.sum_range_succ,← intervalIntegral.integral_add_adjacent_intervals
        (positive_interval_integrable hg (hk (j+1) hj) (hk j hjn.le))
        (positive_interval_integrable hg (hk j hjn.le) hD)]
      linarith
  have hmain := hmenu N le_rfl
  have hdst := (hk N le_rfl).trans_le hstop
  have hnonneg : 0≤∫ t in knee N..dstar, 1/V t := by
    apply intervalIntegral.integral_nonneg hstop
    intro t ht
    exact (one_div_pos.mpr (hp t ((hk N le_rfl).trans_le ht.1))).le
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (positive_interval_integrable hg (hk N le_rfl) hdst)
    (positive_interval_integrable hg hdst hD)
  linarith

/-- The starting condition in the normalized schedule gives `2h/l ≤ h/(1-h)`. -/
theorem potential_knee_le_start {h l : ℝ} (hh : 0<h) (hh1 : h<1) (hl : 2*(1-h)≤l) :
    2*h/l≤h/(1-h) := by
  have hlp : 0<l := by linarith
  apply (div_le_div_iff₀ hlp (sub_pos.mpr hh1)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hl hh.le]

#print axioms potential_knee_le_start
#print axioms potential_integral_bound
#print axioms potential_adjacent_band
end WaringEnvelope
