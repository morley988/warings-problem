import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The actual Waring conclusion and a finite representation count

`WaringBound k s` states that every sufficiently large natural number is a
sum of at most `s` positive integral `k`th powers. It is not an uninterpreted
predicate and it is not defined in terms of a numerical certificate.

The theorems below connect positivity of an explicitly defined finite count
to that conclusion. They do not provide the necessary analytic lower bound
for that count. This is the intended end of a future complete circle-method
formalization.
-/

open scoped BigOperators

namespace Waring

def RepresentableByAtMost (k s n : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ s ∧ ∃ x : Fin t → ℕ,
    (∀ i, 0 < x i) ∧ ∑ i, (x i) ^ k = n

/-- Standard upper-bound formulation, avoiding a choice of a least `G(k)`. -/
def WaringBound (k s : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, RepresentableByAtMost k s n

theorem RepresentableByAtMost.mono {k s t n : ℕ}
    (h : RepresentableByAtMost k s n) (hst : s ≤ t) :
    RepresentableByAtMost k t n := by
  obtain ⟨r, hrs, x, hx, hsum⟩ := h
  exact ⟨r, hrs.trans hst, x, hx, hsum⟩

theorem WaringBound.mono {k s t : ℕ} (h : WaringBound k s) (hst : s ≤ t) :
    WaringBound k t := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => (hN n hn).mono hst⟩

def representationSet (k s n : ℕ) : Finset (Fin s → Fin n) :=
  Finset.univ.filter (fun x => ∑ i, ((x i).val + 1) ^ k = n)

def representationCount (k s n : ℕ) : ℕ :=
  (representationSet k s n).card

theorem representationCount_pos_iff (k s n : ℕ) :
    0 < representationCount k s n ↔
      ∃ x : Fin s → Fin n, ∑ i, ((x i).val + 1) ^ k = n := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨x, hx⟩
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

theorem representable_of_count_pos {k s n : ℕ}
    (h : 0 < representationCount k s n) : RepresentableByAtMost k s n := by
  obtain ⟨x, hx⟩ := (representationCount_pos_iff k s n).mp h
  exact ⟨s, le_rfl, fun i => (x i).val + 1, fun i => Nat.succ_pos _, hx⟩

theorem waringBound_of_eventually_count_pos {k s : ℕ}
    (h : ∃ N : ℕ, ∀ n ≥ N, 0 < representationCount k s n) :
    WaringBound k s := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => representable_of_count_pos (hN n hn)⟩

/-- A real lower bound for the actual counting function supplies the Waring conclusion. -/
theorem waringBound_of_positive_lower_bound {k s : ℕ}
    {scale : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∃ N : ℕ, ∀ n ≥ N,
      0 < scale n ∧ c * scale n ≤ (representationCount k s n : ℝ)) :
    WaringBound k s := by
  apply waringBound_of_eventually_count_pos
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  have hs := hN n hn
  have hr : (0 : ℝ) < representationCount k s n :=
    lt_of_lt_of_le (mul_pos hc hs.1) hs.2
  exact_mod_cast hr

/-- The final positivity step after a major/minor decomposition has been proved. -/
theorem count_pos_of_major_minor {count : ℕ} {major minor scale c : ℝ}
    (hc : 0 < c) (hs : 0 < scale)
    (hdecomp : (count : ℝ) = major + minor)
    (hmajor : c * scale ≤ major)
    (hminor : |minor| ≤ c * scale / 2) : 0 < count := by
  have hneg : - |minor| ≤ minor := neg_abs_le minor
  have hcs : 0 < c * scale := mul_pos hc hs
  have hr : (0 : ℝ) < count := by linarith
  exact_mod_cast hr

/-- This generic endgame is conditional on a decomposition and its estimates,
not on the Waring conclusion itself. -/
theorem waringBound_of_major_minor {k s : ℕ}
    {major minor scale : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∃ N : ℕ, ∀ n ≥ N,
      0 < scale n ∧
      (representationCount k s n : ℝ) = major n + minor n ∧
      c * scale n ≤ major n ∧ |minor n| ≤ c * scale n / 2) :
    WaringBound k s := by
  apply waringBound_of_eventually_count_pos
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hs, hd, hma, hmi⟩ := hN n hn
  exact count_pos_of_major_minor hc hs hd hma hmi

end Waring
