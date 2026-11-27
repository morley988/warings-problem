import Waring.SamplingArithmetic
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# The discrete cubic divisor-class estimate

For `d|h^3`, the least divisibility base is the valuation-wise ceiling cube
root of `d`. It divides every such `h`, and `d≤b^3`. A direct finite sum,
including the zero-error case, gives the improved `H^3/(t+AH^3t)` shape
used in the refined coefficient sampling argument.
-/

noncomputable section
open scoped BigOperators

namespace Waring.CubicDivisorClasses

def base (d : ℕ) : ℕ := Nat.ceilRoot 3 d

theorem base_pos {d : ℕ} (hd : 0 < d) : 0 < base d := by
  exact Nat.pos_of_ne_zero (Nat.ceilRoot_ne_zero.mpr ⟨by norm_num, hd.ne'⟩)

theorem base_dvd_iff (d h : ℕ) : base d ∣ h ↔ d ∣ h ^ 3 :=
  (Nat.dvd_pow_iff_ceilRoot_dvd (by norm_num : (3 : ℕ) ≠ 0)).symm

theorem le_base_cube {d : ℕ} (hd : 0 < d) : d ≤ base d ^ 3 := by
  exact Nat.le_of_dvd (pow_pos (base_pos hd) _)
    (Nat.dvd_ceilRoot_pow (by norm_num : (3 : ℕ) ≠ 0))

theorem base_le_of_nonempty {d h : ℕ} (hh : 0 < h) (hdvd : d ∣ h ^ 3) : base d ≤ h :=
  Nat.le_of_dvd hh ((base_dvd_iff d h).mpr hdvd)

theorem reciprocal_cube_le_telescope {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ 3 ≤ 2 / x - 2 / (x + 1) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxp : 0 < x + 1 := by linarith
  have heq : 2 / x - 2 / (x+1) = 2 / (x * (x+1)) := by field_simp; ring
  rw [heq]
  apply (div_le_div_iff₀ (pow_pos hx0 3) (mul_pos hx0 hxp)).mpr
  have h : x+1 ≤ 2*x^2 := by nlinarith [sq_nonneg (x-1)]
  have hm := mul_le_mul_of_nonneg_left h hx0.le
  nlinarith

theorem finite_reciprocal_cubes (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ)+1)^3) ≤ 2 := by
  have ht : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℝ)+1)^3) ≤
      2 - 2 / ((N : ℝ)+1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ]
        have hh := reciprocal_cube_le_telescope (x := (N : ℝ)+1) (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
        push_cast
        nlinarith
  exact (ht N).trans (sub_le_self _ (by positivity))

def reciprocalClassSum (N : ℕ) (A b : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, 1 / (1 + A * b^3 * ((n : ℝ)+1)^3)

theorem reciprocalClassSum_nonneg (N : ℕ) {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    0 ≤ reciprocalClassSum N A b := by
  exact Finset.sum_nonneg (fun n _ => by positivity)

theorem reciprocalClassSum_trivial (N : ℕ) {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    reciprocalClassSum N A b ≤ (N : ℝ) := by
  have hh : ∀ n : ℕ, 1 / (1 + A * b^3 * ((n : ℝ)+1)^3) ≤ 1 := by
    intro n
    apply (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) _).trans_eq (one_div_one)
    have hterm : 0 ≤ A * b^3 * ((n:ℝ)+1)^3 := by positivity
    linarith
  calc
    reciprocalClassSum N A b ≤ ∑ n ∈ Finset.range N, (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => hh n)
    _ = N := by simp

theorem reciprocalClassSum_decay (N : ℕ) {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    reciprocalClassSum N A b ≤ 2 / (A * b^3) := by
  have hh : ∀ n : ℕ, 1 / (1 + A * b^3 * ((n : ℝ)+1)^3) ≤
      (1 / (A * b^3)) * (1 / ((n : ℝ)+1)^3) := by
    intro n
    have hpos : 0 < A*b^3*((n:ℝ)+1)^3 := by positivity
    calc
      _ ≤ 1 / (A*b^3*((n:ℝ)+1)^3) :=
        one_div_le_one_div_of_le hpos (le_add_of_nonneg_left (by norm_num))
      _ = _ := by rw [one_div_mul_one_div]
  calc
    reciprocalClassSum N A b ≤ ∑ n ∈ Finset.range N,
        (1 / (A * b^3)) * (1 / ((n : ℝ)+1)^3) := Finset.sum_le_sum (fun n _ => hh n)
    _ = (1 / (A * b^3)) * ∑ n ∈ Finset.range N, 1 / ((n : ℝ)+1)^3 := by rw [Finset.mul_sum]
    _ ≤ (1 / (A * b^3)) * 2 :=
      mul_le_mul_of_nonneg_left (finite_reciprocal_cubes N) (by positivity)
    _ = _ := by ring

def classContribution (H d : ℕ) (A t : ℝ) : ℝ :=
  (d : ℝ) / t * reciprocalClassSum (H / base d) A (base d : ℝ)

theorem classContribution_trivial {H d : ℕ} {A t : ℝ}
    (hd : 0 < d) (hbase : base d ≤ H) (hA : 0 ≤ A) (ht : 0 < t) :
    classContribution H d A t ≤ (H : ℝ)^3 / t := by
  have hb : (0 : ℝ) < base d := by exact_mod_cast base_pos hd
  have hdB : (d : ℝ) ≤ (base d : ℝ)^3 := by exact_mod_cast le_base_cube hd
  have hbH : (base d : ℝ) ≤ H := by exact_mod_cast hbase
  have hNb : (H / base d : ℕ) * base d ≤ H := Nat.div_mul_le_self H (base d)
  have hN : ((H / base d : ℕ) : ℝ) ≤ (H : ℝ) / base d := by
    apply (le_div_iff₀ hb).mpr
    exact_mod_cast hNb
  unfold classContribution
  calc
    (d : ℝ) / t * reciprocalClassSum (H / base d) A (base d : ℝ) ≤
        (d : ℝ) / t * (H / base d : ℕ) :=
      mul_le_mul_of_nonneg_left (reciprocalClassSum_trivial _ hA hb.le) (by positivity)
    _ ≤ ((base d : ℝ)^3 / t) * ((H : ℝ) / base d) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hdB ht.le
      · exact hN
      · positivity
      · positivity
    _ = (base d : ℝ)^2 * H / t := by field_simp
    _ ≤ (H : ℝ)^3 / t := by
      apply div_le_div_of_nonneg_right _ ht.le
      have hh := pow_le_pow_left₀ hb.le hbH 2
      have hm := mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤H by positivity)
      nlinarith

theorem classContribution_decay {H d : ℕ} {A t : ℝ}
    (hd : 0 < d) (hA : 0 < A) (ht : 0 < t) :
    classContribution H d A t ≤ 2 / (t*A) := by
  have hb : (0 : ℝ) < base d := by exact_mod_cast base_pos hd
  have hdB : (d : ℝ) ≤ (base d : ℝ)^3 := by exact_mod_cast le_base_cube hd
  unfold classContribution
  calc
    (d : ℝ)/t * reciprocalClassSum (H / base d) A (base d : ℝ) ≤
        (d : ℝ)/t * (2/(A*(base d : ℝ)^3)) :=
      mul_le_mul_of_nonneg_left (reciprocalClassSum_decay _ hA hb) (by positivity)
    _ ≤ ((base d : ℝ)^3)/t * (2/(A*(base d : ℝ)^3)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hdB ht.le) (by positivity)
    _ = 2/(t*A) := by field_simp

/-- The refined discrete class estimate. Its constant is explicit and the
statement includes `A=0`, where no reciprocal-decay hypothesis is needed. -/
theorem classContribution_height_bound {H d : ℕ} {A t : ℝ}
    (hd : 0 < d) (hbase : base d ≤ H) (hA : 0 ≤ A) (ht : 0 < t) :
    classContribution H d A t ≤ 4*(H : ℝ)^3 / (t + A*(H : ℝ)^3*t) := by
  have hH : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le (base_pos hd) hbase)
  have hfirst : classContribution H d A t ≤ (2*(H:ℝ)^3)/t := by
    apply (classContribution_trivial hd hbase hA ht).trans
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith [pow_nonneg hH.le 3]
  have hsecond : 0 < A*(H:ℝ)^3*t →
      classContribution H d A t ≤ (2*(H:ℝ)^3)/(A*(H:ℝ)^3*t) := by
    intro hh
    have hAp : 0 < A := by nlinarith [mul_pos (pow_pos hH 3) ht]
    have hb := classContribution_decay (H := H) hd hAp ht
    have heq : (2*(H:ℝ)^3)/(A*(H:ℝ)^3*t) = 2/(t*A) := by field_simp
    rwa [heq]
  have h := SamplingArithmetic.combine_reciprocal_bounds
    (show 0 ≤ 2*(H:ℝ)^3 by positivity) ht (show 0 ≤ A*(H:ℝ)^3*t by positivity) hfirst hsecond
  convert h using 1 <;> ring

theorem positive_multiples_eq_image (H b : ℕ) (hb : 0 < b) :
    (Finset.Icc 1 H).filter (fun h => b ∣ h) =
      (Finset.range (H / b)).image (fun n => b * (n+1)) := by
  classical
  ext h
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hpos, hupper⟩, ⟨m, rfl⟩⟩
    have hm : 0 < m := by
      by_contra hn
      have hz : m = 0 := by omega
      simp [hz] at hpos
    have hmH : m ≤ H / b := (Nat.le_div_iff_mul_le hb).mpr (by simpa [mul_comm] using hupper)
    refine ⟨m-1, by omega, ?_⟩
    have heq : m-1+1 = m := by omega
    rw [heq]
  · rintro ⟨n, hn, rfl⟩
    have hnH : n+1 ≤ H / b := by omega
    have hupper := (Nat.le_div_iff_mul_le hb).mp hnH
    refine ⟨⟨Nat.mul_pos hb (Nat.succ_pos n), ?_⟩, dvd_mul_right _ _⟩
    simpa [mul_comm] using hupper

def originalClassContribution (H d : ℕ) (A t : ℝ) : ℝ :=
  (d : ℝ) / t * ∑ h ∈ (Finset.Icc 1 H).filter (fun h => d ∣ h^3),
    1 / (1 + A * (h : ℝ)^3)

/-- The actual sampled divisor class is exactly the resummed expression;
there is no unjustified change of index or missing zero shift. -/
theorem originalClassContribution_eq {d : ℕ} (hd : 0 < d) (H : ℕ) (A t : ℝ) :
    originalClassContribution H d A t = classContribution H d A t := by
  classical
  have hf : (Finset.Icc 1 H).filter (fun h => d ∣ h^3) =
      (Finset.Icc 1 H).filter (fun h => base d ∣ h) := by
    ext h
    simp only [Finset.mem_filter, base_dvd_iff]
  unfold originalClassContribution classContribution reciprocalClassSum
  rw [hf, positive_multiples_eq_image H (base d) (base_pos hd), Finset.sum_image]
  · congr 1
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    rw [mul_pow]
    ring
  · intro i hi j hj hij
    have hh := Nat.eq_of_mul_eq_mul_left (base_pos hd) hij
    omega

theorem originalClassContribution_height_bound {H d : ℕ} {A t : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (ht : 0 < t) :
    originalClassContribution H d A t ≤ 4*(H : ℝ)^3 / (t + A*(H : ℝ)^3*t) := by
  by_cases hbase : base d ≤ H
  · rw [originalClassContribution_eq hd H A t]
    exact classContribution_height_bound hd hbase hA ht
  · have hzero : H / base d = 0 := Nat.div_eq_of_lt (lt_of_not_ge hbase)
    rw [originalClassContribution_eq hd H A t]
    simp only [classContribution, hzero, reciprocalClassSum, Finset.sum_range_zero, mul_zero]
    positivity

#print axioms base_dvd_iff
#print axioms classContribution_height_bound
#print axioms originalClassContribution_height_bound

end Waring.CubicDivisorClasses
