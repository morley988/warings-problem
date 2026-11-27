import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # Number of defect iterations required by a real drift envelope -/
noncomputable section
namespace WaringEnvelope
open MeasureTheory Set

/-- A sequence with certified variable decrement reaches the terminal defect.
The final step can cross the threshold by any amount, at a cost of one step. -/
theorem finite_defect_descent (V : ℝ → ℝ) (e : ℕ → ℝ) (D target rate : ℝ)
    (hrate : 0<rate) (htarget : 0≤target) (hD : target≤D) (hinit : e 0≤D)
    (hV : ContinuousOn V (Icc target D)) (hpos : ∀ x∈Icc target D, 0<V x)
    (hmono : MonotoneOn V (Icc target D))
    (hrec : ∀ j, target<e j → e (j+1)≤max 0 (e j-rate*V (e j))) :
    ∃ n : ℕ, e n≤target ∧ (n:ℝ)≤1+(∫ t in target..D, 1/V t)/rate := by
  have hcont : ContinuousOn (fun t => 1/V t) (Icc target D) :=
    continuousOn_const.div hV (fun x hx => (hpos x hx).ne')
  have hint {x y : ℝ} (hx : target≤x) (hxy : x≤y) (hy : y≤D) :
      IntervalIntegrable (fun t => 1/V t) volume x y :=
    ContinuousOn.intervalIntegrable_of_Icc hxy
      (hcont.mono fun t ht => ⟨hx.trans ht.1,ht.2.trans hy⟩)
  have iter (j : ℕ) (hj : ∀ i≤j, target<e i) :
      e j≤D ∧ (j:ℝ)*rate ≤ ∫ x in (e j)..D, 1/V x := by
    induction j with
    | zero =>
      refine ⟨hinit,?_⟩
      simp only [Nat.cast_zero,zero_mul]
      exact intervalIntegral.integral_nonneg hinit
        (fun x hx => (one_div_pos.mpr (hpos x ⟨(hj 0 (by omega)).le.trans hx.1,hx.2⟩)).le)
    | succ j ih =>
      obtain ⟨hu,hp⟩ := ih (fun i hi => hj i (by omega))
      have hnow := hj j (by omega)
      have hnext := hj (j+1) (by omega)
      have hv := hpos _ ⟨hnow.le,hu⟩
      have hstep := (le_max_iff.mp (hrec j hnow)).resolve_left (by linarith)
      have hdec : e (j+1)≤e j := by nlinarith [mul_pos hrate hv]
      have hcharge : rate ≤ ∫ x in (e (j+1))..(e j), 1/V x := by
        calc
          _ ≤ (e j-e (j+1))/V (e j) := (le_div_iff₀ hv).2 (by linarith)
          _ = ∫ _x in (e (j+1))..(e j), 1/V (e j) := by
            rw [intervalIntegral.integral_const,smul_eq_mul];ring
          _ ≤ _ := intervalIntegral.integral_mono_on hdec intervalIntegrable_const
            (hint hnext.le hdec hu) (fun x hx => by
              apply one_div_le_one_div_of_le (hpos x ⟨hnext.le.trans hx.1,hx.2.trans hu⟩)
              exact hmono ⟨hnext.le.trans hx.1,hx.2.trans hu⟩ ⟨hnow.le,hu⟩ hx.2)
      refine ⟨hdec.trans hu,?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint hnext.le hdec hu) (hint hnow.le hu le_rfl)]
      push_cast
      linarith
  have bound (j : ℕ) (hj : ∀ i≤j, target<e i) :
      (j:ℝ)*rate ≤ ∫ x in target..D, 1/V x := by
    obtain ⟨hu,hi⟩ := iter j hj
    have hl := (hj j le_rfl).le
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hl hu) (hint hl hu le_rfl)]
    have hn : 0≤∫ x in target..(e j), 1/V x :=
      intervalIntegral.integral_nonneg hl (fun x hx => (one_div_pos.mpr (hpos x ⟨hx.1,hx.2.trans hu⟩)).le)
    linarith
  have hit : ∃ n, e n≤target := by
    by_contra! h
    obtain ⟨j,hj⟩ := exists_nat_gt ((∫ x in target..D, 1/V x)/rate)
    exact (not_lt_of_ge (bound j (fun i _ => h i))) ((div_lt_iff₀ hrate).mp hj)
  let n := Nat.find hit
  refine ⟨n,Nat.find_spec hit,?_⟩
  cases hn : n with
  | zero =>
    have hi : 0≤∫ x in target..D, 1/V x :=
      intervalIntegral.integral_nonneg hD (fun x hx => (one_div_pos.mpr (hpos x hx)).le)
    simpa only [Nat.cast_zero] using add_nonneg (zero_le_one : (0:ℝ)≤1) (div_nonneg hi hrate.le)
  | succ j =>
    have hp := bound j (fun i hi => lt_of_not_ge (Nat.find_min hit (m:=i) (by change i<n;omega)))
    have hj := (le_div_iff₀ hrate).2 hp
    push_cast
    linarith

#print axioms finite_defect_descent
end WaringEnvelope
