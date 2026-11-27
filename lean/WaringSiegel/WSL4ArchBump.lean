import WaringSiegel.WSL4ArchComplexStationary
import WaringSiegel.WSL4ArchRealStationary
import WaringSiegel.WSL3UnitSmoothSchwartz

/-!
# An explicit product bump equal to one near zero

The local factors and the mixed product are smooth, nonnegative, bounded by
one, equal to one on the half-unit ball, and supported in the unit ball.
The source is defined as a product, so subsequent place factorization is literal.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff SchwartzMap
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

def realNearZeroBump (x : ℝ) : ℝ := Real.smoothTransition (2-4*x^2)
def complexNearZeroBump (z : ℂ) : ℝ := Real.smoothTransition (2-4*Complex.normSq z)

theorem realNearZeroBump_contDiff : ContDiff ℝ ∞ realNearZeroBump := by
  unfold realNearZeroBump
  fun_prop

theorem complexNearZeroBump_contDiff : ContDiff ℝ ∞ complexNearZeroBump :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub
    (contDiff_const.mul complex_normSq_contDiff))

theorem realNearZeroBump_nonneg (x : ℝ) : 0 ≤ realNearZeroBump x :=
  Real.smoothTransition.nonneg _
theorem complexNearZeroBump_nonneg (z : ℂ) : 0 ≤ complexNearZeroBump z :=
  Real.smoothTransition.nonneg _
theorem realNearZeroBump_le_one (x : ℝ) : realNearZeroBump x ≤ 1 :=
  Real.smoothTransition.le_one _
theorem complexNearZeroBump_le_one (z : ℂ) : complexNearZeroBump z ≤ 1 :=
  Real.smoothTransition.le_one _

theorem realNearZeroBump_eq_one {x : ℝ} (hx : |x| ≤ 1/2) :
    realNearZeroBump x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  nlinarith [sq_abs x,abs_nonneg x]

theorem complexNearZeroBump_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    complexNearZeroBump z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z]

theorem realNearZeroBump_support : support realNearZeroBump ⊆ closedBall (0:ℝ) 1 := by
  intro x hx
  have hpos : 0 < 2-4*x^2 :=
    lt_of_not_ge (fun hn => hx (Real.smoothTransition.zero_of_nonpos hn))
  simp only [mem_closedBall,Real.dist_eq,sub_zero]
  nlinarith [sq_abs x,abs_nonneg x]

theorem complexNearZeroBump_support : support complexNearZeroBump ⊆ closedBall (0:ℂ) 1 := by
  intro z hz
  have hpos : 0 < 2-4*Complex.normSq z :=
    lt_of_not_ge (fun hn => hz (Real.smoothTransition.zero_of_nonpos hn))
  rw [Complex.normSq_eq_norm_sq] at hpos
  simp only [mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg z]

theorem realNearZeroBump_complex_support :
    support (fun x => (realNearZeroBump x:ℂ)) ⊆ closedBall (0:ℝ) 1 := by
  intro x hx
  apply realNearZeroBump_support
  change realNearZeroBump x ≠ 0
  intro hz
  apply hx
  simp only [hz,Complex.ofReal_zero]

theorem complexNearZeroBump_complex_support :
    support (fun z => (complexNearZeroBump z:ℂ)) ⊆ closedBall (0:ℂ) 1 := by
  intro z hz
  apply complexNearZeroBump_support
  change complexNearZeroBump z ≠ 0
  intro he
  apply hz
  simp only [he,Complex.ofReal_zero]

theorem realNearZeroBump_norm_le (x : ℝ) : ‖(realNearZeroBump x:ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (realNearZeroBump_nonneg x)]
    using realNearZeroBump_le_one x

theorem complexNearZeroBump_norm_le (z : ℂ) : ‖(complexNearZeroBump z:ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (complexNearZeroBump_nonneg z)]
    using complexNearZeroBump_le_one z

variable {K : Type*} [Field K] [NumberField K]

def nearZeroWeight (x : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, realNearZeroBump (x.1 w)) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, complexNearZeroBump (x.2 w)

theorem nearZeroWeight_contDiff : ContDiff ℝ ∞ (nearZeroWeight (K:=K)) := by
  apply ContDiff.mul
  · apply contDiff_prod
    intro w hw
    exact realNearZeroBump_contDiff.comp ((contDiff_apply ℝ ℝ w).comp contDiff_fst)
  · apply contDiff_prod
    intro w hw
    exact complexNearZeroBump_contDiff.comp ((contDiff_apply ℝ ℂ w).comp contDiff_snd)

theorem nearZeroWeight_nonneg (x : mixedSpace K) : 0 ≤ nearZeroWeight x :=
  mul_nonneg (Finset.prod_nonneg (fun _ _ => realNearZeroBump_nonneg _))
    (Finset.prod_nonneg (fun _ _ => complexNearZeroBump_nonneg _))

theorem nearZeroWeight_le_one (x : mixedSpace K) : nearZeroWeight x ≤ 1 := by
  apply (mul_le_mul _ _ (Finset.prod_nonneg (fun _ _ => complexNearZeroBump_nonneg _))
    zero_le_one).trans_eq (one_mul 1)
  · exact Finset.prod_le_one (fun _ _ => realNearZeroBump_nonneg _)
      (fun _ _ => realNearZeroBump_le_one _)
  · exact Finset.prod_le_one (fun _ _ => complexNearZeroBump_nonneg _)
      (fun _ _ => complexNearZeroBump_le_one _)

theorem nearZeroWeight_eq_one {x : mixedSpace K} (hx : ‖x‖ ≤ 1/2) :
    nearZeroWeight x = 1 := by
  have hv := (mixed_norm_le_iff x (1/2)).mp hx
  have hr (w : {w : InfinitePlace K // IsReal w}) : realNearZeroBump (x.1 w) = 1 := by
    apply realNearZeroBump_eq_one
    simpa only [normAtPlace_apply_of_isReal w.property,Real.norm_eq_abs] using hv w
  have hc (w : {w : InfinitePlace K // IsComplex w}) : complexNearZeroBump (x.2 w) = 1 := by
    apply complexNearZeroBump_eq_one
    simpa only [normAtPlace_apply_of_isComplex w.property] using hv w
  simp only [nearZeroWeight,hr,hc,Finset.prod_const_one,one_mul]

theorem nearZeroWeight_support : support (nearZeroWeight (K:=K)) ⊆ closedBall 0 1 := by
  intro x hx
  have hh := mul_ne_zero_iff.mp hx
  have hr (w : {w : InfinitePlace K // IsReal w}) : |x.1 w| ≤ 1 := by
    have hs := realNearZeroBump_support
      ((Finset.prod_ne_zero_iff.mp hh.1) w (Finset.mem_univ w))
    simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hs
  have hc (w : {w : InfinitePlace K // IsComplex w}) : ‖x.2 w‖ ≤ 1 := by
    have hs := complexNearZeroBump_support
      ((Finset.prod_ne_zero_iff.mp hh.2) w (Finset.mem_univ w))
    simpa only [mem_closedBall,dist_zero_right] using hs
  simp only [mem_closedBall,dist_zero_right]
  apply (mixed_norm_le_iff x 1).mpr
  intro w
  rcases isReal_or_isComplex w with hw | hw
  · simpa only [normAtPlace_apply_of_isReal hw,Real.norm_eq_abs] using hr ⟨w,hw⟩
  · simpa only [normAtPlace_apply_of_isComplex hw] using hc ⟨w,hw⟩

theorem nearZeroWeight_hasCompactSupport : HasCompactSupport (nearZeroWeight (K:=K)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1) nearZeroWeight_support

def nearZeroSchwartz : 𝓢(mixedSpace K,ℂ) :=
  (nearZeroWeight_hasCompactSupport.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp nearZeroWeight_contDiff)

@[simp] theorem nearZeroSchwartz_apply (x : mixedSpace K) :
    nearZeroSchwartz x = (nearZeroWeight x:ℂ) := rfl

/-- The actual product source satisfies all mixed-moment cutoff hypotheses. -/
theorem nearZeroSchwartz_majorant :
    ContDiff ℝ ∞ (nearZeroSchwartz (K:=K)) ∧ HasCompactSupport (nearZeroSchwartz (K:=K)) ∧
      (∀ x : mixedSpace K, ‖x‖ ≤ (1:ℝ)/2 → nearZeroSchwartz x = 1) ∧
      (∀ x : mixedSpace K, nearZeroSchwartz x = (‖nearZeroSchwartz x‖:ℂ)) ∧
      (∀ x : mixedSpace K, ‖nearZeroSchwartz x‖ ≤ 1) ∧
      (∀ x : mixedSpace K, nearZeroSchwartz x ≠ 0 → ‖x‖ ≤ 1) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp nearZeroWeight_contDiff,?_,?_,?_,?_,?_⟩
  · exact nearZeroWeight_hasCompactSupport.comp_left (g:=Complex.ofReal) (by simp)
  · intro x hx
    simp only [nearZeroSchwartz_apply,nearZeroWeight_eq_one hx,Complex.ofReal_one]
  · intro x
    simp only [nearZeroSchwartz_apply,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (nearZeroWeight_nonneg x)]
  · intro x
    simpa only [nearZeroSchwartz_apply,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (nearZeroWeight_nonneg x)] using nearZeroWeight_le_one x
  · intro x hx
    have h : nearZeroWeight x ≠ 0 := by simpa only [nearZeroSchwartz_apply,Complex.ofReal_ne_zero] using hx
    simpa only [mem_closedBall,dist_zero_right] using nearZeroWeight_support h

#print axioms nearZeroSchwartz_majorant
end WaringSiegel.WSL4

