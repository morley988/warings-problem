import Waring.CertificateInterpolation

/-!
# Conditional analytic interpretation of a checked recurrence round

The finite evaluator is not asserted to prove analytic estimates. Instead,
`AnalyticPolicySound` states exactly the missing analytic implication for one
fixed policy. This is an explicit theorem parameter, never an axiom. Subject
to that parameter and actual admissibility of both input curves, a checked
round preserves actual admissibility.
-/

noncomputable section
namespace Waring.Certificate
open Waring.SmoothMoments

/-- Required analytic correctness of one particular policy. Establishing this
property entails the corresponding efficient differences, terminal estimates,
completion and resource lemmas. Numerical evaluator acceptance is insufficient.
-/
def AnalyticPolicySound (k : ℕ) (policy : Policy) : Prop :=
  ∀ (curve coefficient : Curve),
    AdmissibleCurve k curve → AdmissibleCurve (2 * k) coefficient →
    ∀ e : Evaluation, evaluate k curve coefficient policy = some e →
      AdmissibleExponent k (2 * policy.halfOrder) (e.raw : ℝ)

theorem admissible_qmin {k p : ℕ} {x y : Q}
    (hx : AdmissibleExponent k p (x : ℝ))
    (hy : AdmissibleExponent k p (y : ℝ)) :
    AdmissibleExponent k p (qmin x y : ℝ) := by
  by_cases h : x ≤ y
  · simpa only [qmin, if_pos h] using hx
  · simpa only [qmin, if_neg h] using hy

/-- Replacing one finite-table entry by an admissible value is sound. An
out-of-range `set!` leaves the table unchanged. -/
theorem admissibleCurve_set {k : ℕ} {raw : Curve} {i : ℕ} {value : Q}
    (hraw : AdmissibleCurve k raw)
    (hvalue : AdmissibleExponent k (2 * i) (value : ℝ)) :
    AdmissibleCurve k (raw.set! i value) := by
  intro j hj
  simp only [Array.set!_eq_setIfInBounds] at hj ⊢
  have hj' : j < raw.size := by simpa only [Array.size_setIfInBounds] using hj
  rw [getElem!_pos (raw.setIfInBounds i value) j hj, Array.getElem_setIfInBounds hj']
  split
  · rename_i hij
    subst j
    exact hvalue
  · simpa only [getElem!_pos raw j hj'] using hraw j hj'

/-- Finite sequential writes of already established values are safe. The
values themselves may all have been computed from one earlier snapshot. -/
theorem admissibleCurve_fold_updates {k : ℕ} (indices : List ℕ)
    (index : ℕ → ℕ) (value : ℕ → Q) (raw : Curve)
    (hraw : AdmissibleCurve k raw)
    (hvalues : ∀ i ∈ indices, AdmissibleExponent k (2 * index i) (value i : ℝ)) :
    AdmissibleCurve k
      (indices.foldl (fun outputs i => outputs.set! (index i) (value i)) raw) := by
  induction indices generalizing raw with
  | nil => exact hraw
  | cons i indices ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact admissibleCurve_set hraw (hvalues i (List.mem_cons_self ..))
      · intro j hj
        exact hvalues j (List.mem_cons_of_mem i hj)

/-- A checked round has its intended analytic meaning provided the particular
frozen policies have been proved analytically sound and its raw inputs really
are admissible. All such analytic hypotheses remain visible here. -/
theorem checkedRound_admissible_conditional (k : ℕ)
    (policies : Array Policy) (coefficient previous : Curve) (round : Round)
    (hcheck : checkRound k policies coefficient previous round = true)
    (hprevious : AdmissibleCurve k previous)
    (hcoefficient : AdmissibleCurve (2 * k) coefficient)
    (hsound : ∀ i, i < policies.size → AnalyticPolicySound k policies[i]!) :
    AdmissibleCurve k round.outputs := by
  rcases checkRound_sound k policies coefficient previous round hcheck with
    ⟨hinputs, hinterp, _hsize, hentries, houtputs⟩
  have hraw : AdmissibleCurve k round.inputs := hinputs ▸ hprevious
  have hinterpolated : AdmissibleCurve k round.interpolation.values :=
    checkedInterpolation_admissible k round.inputs round.interpolation hinterp hraw
  have hshape := (checkInterpolation_sound round.inputs round.interpolation hinterp).1
  rw [← houtputs]
  unfold updatedCurve
  apply admissibleCurve_fold_updates _ _ _ _ hraw
  intro i hi
  have hi' : i < policies.size := List.mem_range.mp hi
  have he := hentries i hi'
  simp only [checkRoundEntry, Bool.and_eq_true, decide_eq_true_eq] at he
  have hin : policies[i]!.halfOrder < round.interpolation.values.size := hshape ▸ he.1
  have hentry := checkEntry_sound k round.interpolation.values coefficient
    policies[i]! round.entries[i]! he.2
  have hnew := hsound i hi' _ _ hinterpolated hcoefficient _ hentry.1
  have hrounded : AdmissibleExponent k (2 * policies[i]!.halfOrder)
      (round.entries[i]!.rounded : ℝ) :=
    admissibleExponent_mono hnew (by exact_mod_cast hentry.2.1)
  exact admissible_qmin (hinterpolated _ hin) hrounded

#print axioms checkedRound_admissible_conditional

end Waring.Certificate
