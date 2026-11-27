import Waring.ReciprocalSums
import Waring.BasicMatching

/-!
# The nondivisible frequencies in the shallow coefficient argument

A single Dirichlet approximant at twice the full frequency range controls
all frequencies not divisible by its denominator. The estimate is finite
and includes the exact dyadic logarithmic factor.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowSpacing
open RationalHeight

theorem rational_cross_ne_zero (r : ℚ) {n : ℕ} (hn : ¬r.den∣n) (m : ℤ) :
    r.num*(n : ℤ)-(r.den : ℤ)*m≠0 := by
  intro hz
  have hdiv : (r.den : ℤ)∣r.num*(n : ℤ) := ⟨m,sub_eq_zero.mp hz⟩
  have hdivN : r.den∣r.num.natAbs*n := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Int.natCast_dvd.mp hdiv
  exact hn (r.reduced.symm.dvd_of_dvd_mul_left hdivN)

theorem nondivisor_distance_lower (r : ℚ) {α : ℝ} {n : ℕ}
    (hn : ¬r.den∣n) (herr : (n : ℝ)*error α r≤1/2) :
    1/(2*(r.den : ℝ)) ≤ integerDistance (α*(n : ℝ)) := by
  have hq : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  let m : ℤ := round (α*(n : ℝ))
  have hcross := rational_cross_ne_zero r hn m
  have honeZ : (1 : ℤ)≤|r.num*(n : ℤ)-(r.den : ℤ)*m| := by
    have hh := abs_pos.mpr hcross
    omega
  have hone : (1 : ℝ)≤|((r.num*(n : ℤ)-(r.den : ℤ)*m : ℤ) : ℝ)| := by exact_mod_cast honeZ
  have hid : ((r.num*(n : ℤ)-(r.den : ℤ)*m : ℤ) : ℝ)=
      (r.den : ℝ)*(α*(n : ℝ)-(m : ℝ))-(n : ℝ)*((r.den : ℝ)*α-(r.num : ℝ)) := by
    push_cast
    ring
  have htriangle : 1≤(r.den : ℝ)*integerDistance (α*(n : ℝ))+(n : ℝ)*error α r := by
    apply hone.trans
    rw [hid]
    apply (abs_sub _ _).trans
    have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
    simp only [abs_mul,abs_of_pos hq,abs_of_nonneg hn0]
    rfl
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hq)).mpr
  nlinarith only [htriangle,herr]

theorem linearSumBound_nonneg (J : ℕ) (β : ℝ) : 0≤linearSumBound J β := by
  have hd : 0≤ integerDistance β := abs_nonneg _
  unfold linearSumBound
  split_ifs <;> positivity

theorem linearSumBound_le_denominator_cap (r : ℚ) {α : ℝ} {n : ℕ}
    (hn : ¬r.den∣n) (herr : (n : ℝ)*error α r≤1/2) (J : ℕ) :
    linearSumBound J (α*(n : ℝ))≤linearSumBound r.den (α*(n : ℝ)) := by
  have hq : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have hd := nondivisor_distance_lower r hn herr
  have hdp : 0< integerDistance (α*(n : ℝ)) := (by positivity : 0<1/(2*(r.den : ℝ))).trans_le hd
  have hrec : 1/(2*integerDistance (α*(n : ℝ)))≤(r.den : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hdp)).mpr
    have hh := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hq)).mp hd
    nlinarith only [hh]
  simp only [linearSumBound,if_neg hdp.ne',min_eq_right hrec]
  exact min_le_right _ _

/-- Uniform sum over all nonmultiples of the approximant denominator. -/
theorem nondivisor_kernel_sum (r : ℚ) {α : ℝ} {T : ℕ} (hT : 0<T)
    (hq : (r.den : ℝ)≤2*(T : ℝ)) (herr : 2*(T : ℝ)*error α r≤1)
    (J L : ℕ) (hL : (r.den : ℝ)≤2^L) :
    (∑n∈(Finset.Icc 1 T).filter (fun n=>¬r.den∣n),linearSumBound J (α*(n : ℝ)))≤
      128*(T : ℝ)*(L+1 : ℕ) := by
  have hgood : (r.den : ℝ)*|(r.den : ℝ)*α-(r.num : ℝ)|≤1 := by
    exact (mul_le_mul_of_nonneg_right hq (error_nonneg α r)).trans herr
  have hsub : (Finset.Icc 1 T).filter (fun n=>¬r.den∣n)⊆Finset.range (T+1) := by
    intro n hn
    have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Finset.mem_range.mpr (by omega)
  calc
    _ ≤ ∑n∈(Finset.Icc 1 T).filter (fun n=>¬r.den∣n),linearSumBound r.den (α*(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn,hndiv⟩ := Finset.mem_filter.mp hn
      apply linearSumBound_le_denominator_cap r hndiv _ J
      have hle : (n : ℝ)≤T := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      have hh := mul_le_mul_of_nonneg_right hle (error_nonneg α r)
      linarith
    _ ≤ ∑n∈Finset.range (T+1),linearSumBound r.den (α*(n : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _=>linearSumBound_nonneg _ _)
    _ ≤ 16*((T+1 : ℕ)*(r.den : ℝ)/r.den+(T+1 : ℕ)+r.den+r.den)*(L+1 : ℕ) :=
      ReciprocalSums.linearSumBound_sum_denominator r hgood (T+1) r.den L r.pos hL
    _ ≤ 128*(T : ℝ)*(L+1 : ℕ) := by
      have hq0 : (r.den : ℝ)≠0 := by exact_mod_cast r.den_nz
      rw [mul_div_cancel_right₀ _ hq0]
      push_cast
      have hT1 : (1 : ℝ)≤T := by exact_mod_cast hT
      have hh : 16*((T : ℝ)+1+(T+1)+r.den+r.den)≤128*T := by linarith
      exact mul_le_mul_of_nonneg_right hh (by positivity)

#print axioms nondivisor_distance_lower
#print axioms nondivisor_kernel_sum
end Waring.PolicyCompletionShallowSpacing
