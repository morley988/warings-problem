import Lean

/-! The word metric for the three generators (1,0), (0,1), (-1,-1)
of (ℤ/mℤ)². With c diagonal steps, the least possible multiplicities
of the first two steps are the reduced residues of x+c and y+c. -/

namespace WaringLinear.ThreeDirections

def wordCost (m x y c : Nat) : Nat :=
  (x + c) % m + (y + c) % m + c

private theorem mod_below_twice {m z : Nat} (hz : z < 2 * m) :
    z % m = if z < m then z else z - m := by
  split
  next h => exact Nat.mod_eq_of_lt h
  next h =>
    rw [Nat.mod_eq_sub_mod (by omega : z ≥ m)]
    exact Nat.mod_eq_of_lt (by omega)

private theorem cost_formula {m x y c : Nat}
    (hx : x < m) (hy : y < m) (hc : c < m) :
    wordCost m x y c =
      (if x + c < m then x + c else x + c - m) +
      (if y + c < m then y + c else y + c - m) + c := by
  unfold wordCost
  rw [mod_below_twice (z := x + c) (by omega),
      mod_below_twice (z := y + c) (by omega)]

private theorem upper_ordered {m x y : Nat}
    (hm : 2 ≤ m) (h3 : m % 3 ≠ 0) (hxy : x ≤ y) (hy : y < m) :
    ∃ c, wordCost m x y c ≤ m - 1 := by
  have hx : x < m := by omega
  by_cases h0 : x + y < m
  · refine ⟨0, ?_⟩
    simp only [wordCost, Nat.add_zero, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    omega
  have hpos : 0 < x := by omega
  by_cases h1 : x + 2*m < m + 2*y
  · refine ⟨m-y, ?_⟩
    rw [cost_formula hx hy (by omega)]
    split <;> split <;> omega
  · refine ⟨m-x, ?_⟩
    rw [cost_formula hx hy (by omega)]
    split <;> split <;> omega

/-- No residue pair needs m steps if 3 does not divide m. -/
theorem diameter_upper {m x y : Nat} (hm : 2 ≤ m) (h3 : m % 3 ≠ 0)
    (hx : x < m) (hy : y < m) : ∃ c, wordCost m x y c ≤ m - 1 := by
  by_cases h : x ≤ y
  · exact upper_ordered hm h3 h hy
  · obtain ⟨c, hc⟩ := upper_ordered hm h3 (by omega : y ≤ x) hx
    exact ⟨c, by simpa only [wordCost, Nat.add_comm ((y+c)%m) ((x+c)%m)] using hc⟩

private theorem lower_for_pair {m x y : Nat} (hx : x < m) (hy : y < m)
    (hxy : x ≤ y) (h0 : m - 1 ≤ x+y)
    (h1 : m-1 + 2*y ≤ x+2*m) (h2 : m-1 + 2*x ≤ m+y)
    (c : Nat) : m - 1 ≤ wordCost m x y c := by
  by_cases hc : c < m
  · rw [cost_formula hx hy hc]
    split <;> split <;> omega
  · unfold wordCost
    omega

/-- The two residue pairs nearest the continuous hole give the sharp
integer diameter m−1 in both nonzero congruence classes modulo 3. -/
theorem diameter_attained {m : Nat} (hm : 2 ≤ m) (h3 : m % 3 ≠ 0) :
    ∃ x < m, ∃ y < m, ∀ c, m-1 ≤ wordCost m x y c := by
  let j := m / 3
  have hj : m = 3*j + m%3 := by dsimp [j]; omega
  by_cases h : m%3 = 1
  · refine ⟨j, by omega, 2*j+1, by omega, ?_⟩
    intro c
    exact lower_for_pair (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) c
  · have h' : m%3 = 2 := by omega
    refine ⟨j+1, by omega, 2*j+1, by omega, ?_⟩
    intro c
    exact lower_for_pair (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) c

#print axioms diameter_upper
#print axioms diameter_attained
end WaringLinear.ThreeDirections
