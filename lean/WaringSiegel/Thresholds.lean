import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact arithmetic for the proposed Waring–Siegel analytic thresholds

These theorems verify the threshold formulas and their optimization. They
do not assert estimates for exponential sums or representations by powers.
The local conditions of the analytic theorem are not removed by arithmetic.
-/

namespace WaringSiegel.Thresholds

/-- First interpolation threshold, with subtraction in the rationals. -/
def first (k r : ℚ) : ℚ := k ^ 2 - r * (k - r - 1) / (k - r + 1)

/-- Classical Hua interpolation threshold. -/
def second (k : ℚ) (j : ℕ) : ℚ :=
  k ^ 2 - (k * (j : ℚ) - (2 : ℚ) ^ j) / (k + 1 - (j : ℚ))

/-- Every index 1,...,k occurs in each branch. -/
def candidates (k : ℕ) : List ℚ :=
  (List.range k).map (fun r : ℕ => first (k : ℚ) ((r + 1 : ℕ) : ℚ)) ++
  (List.range k).map (fun j : ℕ => second (k : ℚ) (j + 1))

/-- The sentinel is strictly above the first branch for k≥3. -/
def threshold (k : ℕ) : ℚ :=
  (candidates k).foldr min ((k : ℚ) ^ 2 + 1)

/-- Least integer strictly above the displayed rational threshold.
The independently treated quadratic case is explicitly set to five. -/
def sufficientVariables (k : ℕ) : ℤ :=
  if k = 2 then 5 else ⌊threshold k⌋ + 1

theorem strict_floor_threshold (b : ℚ) : b < ((⌊b⌋ + 1 : ℤ) : ℚ) := by
  exact_mod_cast Int.lt_floor_add_one b

theorem strict_floor_threshold_minimal (b : ℚ) (s : ℤ) :
    (⌊b⌋ + 1 ≤ s) ↔ b < (s : ℚ) := by
  rw [Int.add_one_le_iff, Int.floor_lt]

theorem foldr_min_le_member (xs : List ℚ) (base x : ℚ) (hx : x ∈ xs) :
    xs.foldr min base ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hx)

theorem threshold_le_first (k r : ℕ) (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    threshold k ≤ first k r := by
  unfold threshold
  apply foldr_min_le_member (candidates k) ((k : ℚ)^2 + 1) (first k r)
  unfold candidates
  apply List.mem_append.mpr
  left
  apply List.mem_map.mpr
  refine ⟨r - 1, ?_, ?_⟩
  · show r - 1 ∈ List.range k
    exact List.mem_range.mpr (by omega)
  · congr 1
    exact_mod_cast (show r - 1 + 1 = r by omega)

theorem first_one_lt_square (k : ℚ) (hk : 2 < k) : first k 1 < k ^ 2 := by
  unfold first
  have hden : k - 1 + 1 = k := by ring
  rw [hden]
  have hnum : 0 < (1 : ℚ) * (k - 1 - 1) := by linarith
  exact sub_lt_self _ (div_pos hnum (by linarith))

theorem threshold_lt_square (k : ℕ) (hk : 3 ≤ k) : threshold k < (k : ℚ) ^ 2 := by
  exact (threshold_le_first k 1 (by omega) (by omega)).trans_lt
    (first_one_lt_square k (by exact_mod_cast (show 2 < k by omega)))

theorem sufficientVariables_le_square (k : ℕ) (hk : 3 ≤ k) :
    sufficientVariables k ≤ (k : ℤ) ^ 2 := by
  unfold sufficientVariables
  rw [if_neg (by omega)]
  apply (strict_floor_threshold_minimal _ _).mpr
  exact_mod_cast threshold_lt_square k hk

/-- Exact reparametrization q=k-r+1 of the first branch. -/
theorem first_reparametrized (k q : ℚ) (hq : q ≠ 0) :
    first k (k - q + 1) = k ^ 2 - k - 3 + (q + (2 * k + 2) / q) := by
  unfold first
  have hd : k - (k - q + 1) + 1 = q := by ring
  rw [hd]
  field_simp
  <;> ring

/-- Successive differences determine the discrete optimizer. -/
theorem successive_difference (a q : ℚ) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) :
    ((q + 1) + a / (q + 1)) - (q + a / q) =
      1 - a / (q * (q + 1)) := by
  field_simp
  <;> ring

/-- The two neighboring inequalities certify a global integer minimum. -/
theorem discrete_minimizer (a : ℚ) (q t : ℕ)
    (hq : 0 < q) (ht : 0 < t)
    (hlo : (q : ℚ) * ((q : ℚ) - 1) ≤ a)
    (hhi : a ≤ (q : ℚ) * ((q : ℚ) + 1)) :
    (q : ℚ) + a / q ≤ (t : ℚ) + a / t := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have ht' : (0 : ℚ) < t := by exact_mod_cast ht
  have heq (u : ℚ) (hu : u ≠ 0) : u + a / u = (u ^ 2 + a) / u := by
    field_simp
  rw [heq _ hq'.ne', heq _ ht'.ne', div_le_div_iff₀ hq' ht']
  rcases lt_trichotomy q t with hqt | hqt | htq
  · have hqt' : (q : ℚ) + 1 ≤ t := by exact_mod_cast (show q + 1 ≤ t by omega)
    have hprod : a ≤ (q : ℚ) * t := by nlinarith
    have hnonneg : 0 ≤ ((t : ℚ) - q) * ((q : ℚ) * t - a) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · subst t
    exact le_rfl
  · have htq' : (t : ℚ) + 1 ≤ q := by exact_mod_cast (show t + 1 ≤ q by omega)
    have hprod : (q : ℚ) * t ≤ a := by nlinarith
    have hnonneg : 0 ≤ ((q : ℚ) - t) * (a - (q : ℚ) * t) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- The claimed saving is algebraically equivalent to the strict first threshold. -/
theorem first_saving_iff (k r s : ℚ)
    (hden : 0 < k * (k + 1) - r * (r + 1)) (hkr : 0 < k - r + 1) :
    0 < 1 - (k - r + 1) * (k * (k + 1) - s) /
      (k * (k + 1) - r * (r + 1)) ↔ first k r < s := by
  unfold first
  rw [sub_pos, div_lt_one hden]
  have heq : k ^ 2 - r * (k-r-1)/(k-r+1) < s ↔
      k ^ 2 - s < r * (k-r-1)/(k-r+1) := by
    constructor <;> intro h <;> linarith
  rw [heq, lt_div_iff₀ hkr]
  constructor <;> intro h <;> nlinarith

end WaringSiegel.Thresholds
