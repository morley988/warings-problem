import Waring.CubicDivisorClasses
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The cube-root alternative in the divisor-class argument

A termwise cubic inequality gives a harmonic loss. That loss is harmless
under the usual epsilon convention, and avoids any unproved comparison
with an improper integral. The discrete estimate includes zero error.
-/

noncomputable section
open scoped BigOperators

namespace Waring.CubicDivisorClasses

theorem cubic_root_term {d t b n H A : ℝ}
    (hd : 0 ≤ d) (ht : 0 < t) (hb : 0 ≤ b) (hn : 0 < n) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hdt : d ≤ t) (hdb : d ≤ b^3) (hbn : b*n ≤ H) :
    (d/t)/(1+A*(b*n)^3) ≤ (H/(t+A*H^3*t)^(1/3:ℝ))/n := by
  let L := t+A*H^3*t
  let Q := 1+A*(b*n)^3
  have hL : 0 < L := by dsimp [L]; positivity
  have hQ : 1 ≤ Q := by
    have hh : 0 ≤ A*(b*n)^3 := by positivity
    dsimp [Q]
    linarith
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hr : 0 < L^(1/3:ℝ) := Real.rpow_pos_of_pos hL _
  have hroot : (L^(1/3:ℝ))^3 = L := by
    rw [← Real.rpow_mul_natCast hL.le]
    norm_num
  have hd3 : d^3 ≤ t^2*b^3 := by
    have hh := mul_le_mul (pow_le_pow_left₀ hd hdt 2) hdb hd (sq_nonneg t)
    nlinarith only [hh]
  have hbn3 : (b*n)^3 ≤ H^3 := pow_le_pow_left₀ (mul_nonneg hb hn.le) hbn 3
  have hQ3 : Q ≤ Q^3 := by nlinarith [sq_nonneg (Q-1)]
  have hcube : (d*n*L^(1/3:ℝ))^3 ≤ (H*t*Q)^3 := by
    calc
      _ = d^3*n^3*L := by rw [mul_pow, mul_pow, hroot]
      _ ≤ (t^2*b^3)*n^3*L := by gcongr
      _ = t^3*((b*n)^3+A*H^3*(b*n)^3) := by dsimp [L]; ring
      _ ≤ t^3*(H^3+A*H^3*(b*n)^3) := by gcongr
      _ = H^3*t^3*Q := by dsimp [Q]; ring
      _ ≤ H^3*t^3*Q^3 := mul_le_mul_of_nonneg_left hQ3 (by positivity)
      _ = _ := by ring
  have hh := le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ)≠0)
    (show 0 ≤ H*t*Q by positivity) hcube
  change (d/t)/Q ≤ (H/L^(1/3:ℝ))/n
  rw [div_div, div_div]
  apply (div_le_div_iff₀ (mul_pos ht hQpos) (mul_pos hr hn)).mpr
  convert hh using 1 <;> ring

/-- Harmonic domination of a single actual divisor class. The extra
`d <= t` is automatic because the classes are divisors of the common
approximant denominator. -/
theorem classContribution_cube_root {H d : ℕ} {A t : ℝ}
    (hH : 0 < H) (hd : 0 < d) (hA : 0 ≤ A) (ht : 0 < t)
    (hdt : (d:ℝ) ≤ t) :
    classContribution H d A t ≤
      (H:ℝ)/(t+A*(H:ℝ)^3*t)^(1/3:ℝ) * (1+Real.log (H:ℝ)) := by
  let b := base d
  let N := H/b
  let K := (H:ℝ)/(t+A*(H:ℝ)^3*t)^(1/3:ℝ)
  have hb : 0 < b := base_pos hd
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hdb : (d:ℝ) ≤ (b:ℝ)^3 := by exact_mod_cast le_base_cube hd
  have hterm (n : ℕ) (hn : n ∈ Finset.range N) :
      (d:ℝ)/t*(1/(1+A*(b:ℝ)^3*((n:ℝ)+1)^3)) ≤ K*(1/((n:ℝ)+1)) := by
    have hnN : n+1 ≤ H/b := by
      have hh : n < H/b := by simpa only [Finset.mem_range, N] using hn
      omega
    have hbmul : b*(n+1) ≤ H := by
      have hh := (Nat.le_div_iff_mul_le hb).mp hnN
      simpa [mul_comm] using hh
    have hh := cubic_root_term (d := (d:ℝ)) (t := t) (b := (b:ℝ))
      (n := (n:ℝ)+1) (H := (H:ℝ)) (A := A) (by positivity) ht hbr.le
      (by positivity) (by positivity) hA hdt hdb (by exact_mod_cast hbmul)
    dsimp [K]
    convert hh using 1 <;> ring
  have hNle : N ≤ H := Nat.div_le_self H b
  have hsum : (∑ n ∈ Finset.range N, 1/((n:ℝ)+1)) ≤ 1+Real.log (H:ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range H, 1/((n:ℝ)+1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNle) (fun n _ _ => by positivity)
      _ = (harmonic H:ℝ) := by simp [harmonic, one_div]
      _ ≤ _ := harmonic_le_one_add_log H
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    classContribution H d A t = ∑ n ∈ Finset.range N,
        (d:ℝ)/t*(1/(1+A*(b:ℝ)^3*((n:ℝ)+1)^3)) := by
      simp only [classContribution, reciprocalClassSum, b, N, Finset.mul_sum]
    _ ≤ ∑ n ∈ Finset.range N, K*(1/((n:ℝ)+1)) := Finset.sum_le_sum hterm
    _ = K*∑ n ∈ Finset.range N, 1/((n:ℝ)+1) := by rw [Finset.mul_sum]
    _ ≤ K*(1+Real.log (H:ℝ)) := mul_le_mul_of_nonneg_left hsum hK

theorem originalClassContribution_cube_root {H d : ℕ} {A t : ℝ}
    (hH : 0 < H) (hd : 0 < d) (hA : 0 ≤ A) (ht : 0 < t)
    (hdt : (d:ℝ) ≤ t) :
    originalClassContribution H d A t ≤
      (H:ℝ)/(t+A*(H:ℝ)^3*t)^(1/3:ℝ)*(1+Real.log (H:ℝ)) := by
  rw [originalClassContribution_eq hd H A t]
  exact classContribution_cube_root hH hd hA ht hdt

#print axioms cubic_root_term
#print axioms originalClassContribution_cube_root

end Waring.CubicDivisorClasses
