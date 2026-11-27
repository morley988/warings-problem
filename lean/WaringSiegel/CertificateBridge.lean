import WaringSiegel.Thresholds
import WaringSiegel.IntegerCertificates

/-!
# The integer certificates imply the exact rational threshold values

This bridge connects the standalone kernel computations to the manuscript's
two rational interpolation formulas and their strict floor endpoint.
-/

namespace WaringSiegel.Thresholds
open IntegerCertificates

theorem first_as_fraction (k r : ℕ)
    (hd : (denominator k r : ℚ) ≠ 0) :
    first k r = (firstNumerator k r : ℚ) / (denominator k r : ℚ) := by
  have hd' : (k : ℚ) - r + 1 ≠ 0 := by simpa [denominator] using hd
  unfold first firstNumerator denominator
  push_cast
  field_simp [hd']

theorem second_as_fraction (k j : ℕ)
    (hd : (denominator k j : ℚ) ≠ 0) :
    second k j = (secondNumerator k j : ℚ) / (denominator k j : ℚ) := by
  have hd' : (k : ℚ) + 1 - j ≠ 0 := by
    have h : (k : ℚ) - j + 1 ≠ 0 := by simpa [denominator] using hd
    convert h using 1 <;> ring
  unfold second secondNumerator denominator
  push_cast
  have he : (k : ℚ) - j + 1 = k + 1 - j := by ring
  rw [he]
  field_simp [hd']

theorem le_foldr_min (xs : List ℚ) (base lower : ℚ)
    (hb : lower ≤ base) (hx : ∀ x ∈ xs, lower ≤ x) :
    lower ≤ xs.foldr min base := by
  induction xs with
  | nil => exact hb
  | cons a xs ih =>
    simp only [List.foldr_cons]
    apply le_min
    · exact hx a (by simp)
    · exact ih (fun x h => hx x (by simp [h]))

theorem threshold_le_second (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    threshold k ≤ second k j := by
  unfold threshold
  apply foldr_min_le_member (candidates k) ((k : ℚ)^2 + 1) (second k j)
  unfold candidates
  apply List.mem_append.mpr
  right
  apply List.mem_map.mpr
  refine ⟨j-1, ?_, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · congr 1
    omega

theorem certificate_exact_value {k s : ℕ} (hk : 3 ≤ k)
    (hc : ThresholdCertificate k s) : sufficientVariables k = (s : ℤ) := by
  obtain ⟨hfirst, hsecond, hupper⟩ := hc
  have hf (r : Fin k) : (s : ℚ) - 1 ≤ first k ((r.val+1 : ℕ) : ℚ) := by
    have hd : (0 : ℚ) < denominator k (r.val+1) := by exact_mod_cast (hfirst r).1
    rw [first_as_fraction k (r.val+1) hd.ne', le_div_iff₀ hd]
    exact_mod_cast (hfirst r).2
  have hs (j : Fin k) : (s : ℚ) - 1 ≤ second k (j.val+1) := by
    have hd : (0 : ℚ) < denominator k (j.val+1) := by exact_mod_cast (hsecond j).1
    rw [second_as_fraction k (j.val+1) hd.ne', le_div_iff₀ hd]
    exact_mod_cast (hsecond j).2
  have hb : (s : ℚ) - 1 ≤ (k : ℚ)^2 + 1 := by
    have hfirst1 := hf ⟨0, by omega⟩
    have hlt := first_one_lt_square (k : ℚ) (by exact_mod_cast (show 2 < k by omega))
    norm_num at hfirst1
    linarith
  have hlow : (s : ℚ) - 1 ≤ threshold k := by
    apply le_foldr_min (candidates k) ((k : ℚ)^2+1) ((s : ℚ)-1) hb
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact hf ⟨r, List.mem_range.mp hr⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact hs ⟨j, List.mem_range.mp hj⟩
  have hupp : threshold k < (s : ℚ) := by
    rcases hupper with ⟨r, hr⟩ | ⟨j, hj⟩
    · apply (threshold_le_first k (r.val+1) (by omega) (by omega)).trans_lt
      have hd : (0 : ℚ) < denominator k (r.val+1) := by exact_mod_cast (hfirst r).1
      rw [first_as_fraction k (r.val+1) hd.ne', div_lt_iff₀ hd]
      exact_mod_cast hr
    · apply (threshold_le_second k (j.val+1) (by omega) (by omega)).trans_lt
      have hd : (0 : ℚ) < denominator k (j.val+1) := by exact_mod_cast (hsecond j).1
      rw [second_as_fraction k (j.val+1) hd.ne', div_lt_iff₀ hd]
      exact_mod_cast hj
  have hflo : ⌊threshold k⌋ = (s : ℤ)-1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hlow
    · simpa using hupp
  unfold sufficientVariables
  rw [if_neg (by omega), hflo]
  omega

end WaringSiegel.Thresholds
