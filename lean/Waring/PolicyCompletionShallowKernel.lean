import Waring.PolicyCompletionShallowArithmetic
import Waring.PolicyCompletionShallowSpacing
import Waring.PolicyCompletionBasicCubic

/-!
# The common-rational kernel for the shallow source estimate

Divisible frequencies retain their exact real error, including error zero.
The remaining frequencies are grouped using the actual three-divisor
injection and the proved finite reciprocal-spacing estimate.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowKernel
open RationalHeight PolicyCompletionBasicCubic PolicyCompletionShallowArithmetic
open PolicyCompletionShallowSpacing

theorem integerDistance_eq_abs_near {x : ℝ} (hx : |x|≤1/2) : integerDistance x=|x| := by
  by_cases hlt : x<1/2
  · have hr : round x=0 := round_eq_zero_iff.mpr ⟨(abs_le.mp hx).1,hlt⟩
    simp only [integerDistance,hr,Int.cast_zero,sub_zero]
  · have he : x=1/2 := le_antisymm (abs_le.mp hx).2 (le_of_not_gt hlt)
    rw [he]
    norm_num [integerDistance,round_eq]

theorem integerDistance_sub_int (x : ℝ) (m : ℤ) : integerDistance (x-(m : ℝ))=integerDistance x := by
  simp only [integerDistance,round_sub_intCast,Int.cast_sub]
  congr 1
  ring

theorem integerDistance_near_int {x : ℝ} (m : ℤ) (hm : |x-(m : ℝ)|≤1/2) :
    integerDistance x=|x-(m : ℝ)| := by
  rw [← integerDistance_sub_int x m]
  exact integerDistance_eq_abs_near hm

theorem divisible_distance_eq (r : ℚ) {α : ℝ} {n : ℕ} (hn : r.den∣n)
    (herr : (n : ℝ)*error α r≤1/2) :
    integerDistance (α*(n : ℝ))=|α-(r : ℝ)| *(n : ℝ) := by
  obtain ⟨c,hc⟩ := hn
  let m : ℤ := r.num*(c : ℤ)
  have hqR : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have hq1 : (1 : ℝ)≤r.den := by exact_mod_cast r.pos
  have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hrat : (r : ℝ)*(n : ℝ)=(m : ℝ) := by
    rw [hc,Rat.cast_def]
    dsimp [m]
    push_cast
    field_simp
  have heq : α*(n : ℝ)-(m : ℝ)=(α-(r : ℝ))*(n : ℝ) := by rw [← hrat]; ring
  have hnear : |α*(n : ℝ)-(m : ℝ)|≤1/2 := by
    rw [heq,abs_mul,abs_of_nonneg hn0]
    have he : error α r=(r.den : ℝ)*|α-(r : ℝ)| := denominator_error α r
    rw [he] at herr
    have hh := mul_le_mul_of_nonneg_right hq1
      (show 0≤|α-(r : ℝ)| *(n : ℝ) by positivity)
    nlinarith only [herr,hh]
  rw [integerDistance_near_int m hnear,heq,abs_mul,abs_of_nonneg hn0]

/-- The actual divisible geometric kernel, with the approximation error
kept in a smooth denominator. No division by zero error is used. -/
theorem divisible_linear_kernel_le (r : ℚ) {α : ℝ} {n : ℕ} (hn : r.den∣n)
    (herr : (n : ℝ)*error α r≤1/2) (J : ℕ) :
    linearSumBound J (α*(n : ℝ))≤2*(J : ℝ)/(1+(J : ℝ)*|α-(r : ℝ)| *(n : ℝ)) := by
  have hh := linearSumBound_le_smooth_kernel J (α*(n : ℝ))
  rw [divisible_distance_eq r hn herr] at hh
  simpa only [mul_assoc] using hh

/-- The complete nondivisible contribution for an arbitrary actual
positive-pair family inside the frequency interval [1,T]. -/
theorem nondivisor_frequency_sum {k : ℕ} (hk : 0<k) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : ℕ,0<T→∀S : Finset (ℕ×(ℕ×ℕ)),
      (∀v∈S,v.2.1<v.2.2)→(∀v∈S,differenceFrequency k v∈Finset.Icc 1 T)→
      ∀r : ℚ,∀α : ℝ,(r.den : ℝ)≤2*(T : ℝ)→2*(T : ℝ)*error α r≤1→
      ∀J L : ℕ,(r.den : ℝ)≤2^L→
      (∑v∈S.filter (fun v=>¬r.den∣differenceFrequency k v),
        linearSumBound J (α*(differenceFrequency k v : ℝ)))≤C*(T : ℝ)^(ε+1)*(L+1 : ℕ) := by
  obtain ⟨C,hC,hgroup⟩ := weighted_differenceFrequency_grouping hk hε
  refine ⟨128*C,by positivity,?_⟩
  intro T hT S hS hmap r α hq herr J L hL
  let F : ℕ→ℝ := fun n=>if ¬r.den∣n then linearSumBound J (α*(n : ℝ)) else 0
  have hF : ∀n∈Finset.Icc 1 T,0≤F n := by
    intro n hn
    dsimp [F]
    split_ifs <;> first | exact linearSumBound_nonneg _ _ | exact le_rfl
  have hg := hgroup T S F hS hmap hF
  have hbound := nondivisor_kernel_sum r hT hq herr J L hL
  have hTpos : (0 : ℝ)<T := by exact_mod_cast hT
  calc
    _ = ∑v∈S,F (differenceFrequency k v) := by rw [Finset.sum_filter]
    _ ≤ C*(T : ℝ)^ε*(∑n∈Finset.Icc 1 T,F n) := hg
    _ = C*(T : ℝ)^ε*(∑n∈(Finset.Icc 1 T).filter (fun n=>¬r.den∣n),linearSumBound J (α*(n : ℝ))) := by
      rw [Finset.sum_filter]
    _ ≤ C*(T : ℝ)^ε*(128*(T : ℝ)*(L+1 : ℕ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (128*C)*(T : ℝ)^(ε+1)*(L+1 : ℕ) := by
      rw [Real.rpow_add hTpos,Real.rpow_one]
      ring

#print axioms divisible_distance_eq
#print axioms nondivisor_frequency_sum
end Waring.PolicyCompletionShallowKernel
