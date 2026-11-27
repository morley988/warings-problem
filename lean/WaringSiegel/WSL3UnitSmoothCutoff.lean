import WaringSiegel.WSL2UnitNodeBoxes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A fixed smooth product cutoff majorizing the positive root box

The cutoff is explicit: smooth transition windows at real places and smooth
windows in the squared complex norm at complex places. It is one on the
inner root box, lies in [0,1], and is supported in a larger positive box still
separated from zero in every embedding. A single fixed weight suffices.
-/
noncomputable section
open MeasureTheory
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

/-- A smooth window equal to one throughout [a,b], supported in (a/2,2b). -/
def positiveSmoothWindow (a b t : ℝ) : ℝ :=
  Real.smoothTransition (2*t/a - 1) * Real.smoothTransition (2-t/b)

theorem positiveSmoothWindow_contDiff (a b : ℝ) : ContDiff ℝ ∞ (positiveSmoothWindow a b) := by
  unfold positiveSmoothWindow
  fun_prop

theorem positiveSmoothWindow_nonneg (a b t : ℝ) : 0 ≤ positiveSmoothWindow a b t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem positiveSmoothWindow_le_one (a b t : ℝ) : positiveSmoothWindow a b t ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem positiveSmoothWindow_eq_one {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hat : a ≤ t) (htb : t ≤ b) : positiveSmoothWindow a b t = 1 := by
  have h₁ : 1 ≤ 2*t/a - 1 := by
    have := (le_div_iff₀ ha).mpr (show 2*a ≤ 2*t by linarith)
    linarith
  have h₂ : 1 ≤ 2-t/b := by
    have : t/b ≤ 1 := (div_le_iff₀ hb).mpr (by simpa using htb)
    linarith
  rw [positiveSmoothWindow, Real.smoothTransition.one_of_one_le h₁,
    Real.smoothTransition.one_of_one_le h₂, mul_one]

theorem positiveSmoothWindow_support {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : positiveSmoothWindow a b t ≠ 0) : a/2 < t ∧ t < 2*b := by
  have h := mul_ne_zero_iff.mp ht
  have h₁ : 0 < 2*t/a - 1 := lt_of_not_ge (fun hn => h.1 (Real.smoothTransition.zero_of_nonpos hn))
  have h₂ : 0 < 2-t/b := lt_of_not_ge (fun hn => h.2 (Real.smoothTransition.zero_of_nonpos hn))
  have h₁' : a < 2*t := by
    have hdiv : 1 < 2*t/a := by linarith
    simpa using (lt_div_iff₀ ha).mp hdiv
  have h₂' : t < 2*b := (div_lt_iff₀ hb).mp (by linarith : t/b < 2)
  exact ⟨by linarith, h₂'⟩

theorem complex_normSq_contDiff : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ => z.re * z.re + z.im * z.im) :=
    (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  simpa only [Complex.normSq_apply] using h

/-- The product structure agrees with the real/complex place decomposition. -/
def smoothRootWeight (ρ R : ℝ) (x : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, positiveSmoothWindow ρ R (x.1 w)) *
    ∏ w : {w : InfinitePlace K // IsComplex w},
      positiveSmoothWindow (ρ^2) (R^2) (Complex.normSq (x.2 w))

theorem smoothRootWeight_contDiff (ρ R : ℝ) : ContDiff ℝ ∞ (smoothRootWeight (K := K) ρ R) := by
  apply ContDiff.mul
  · apply contDiff_prod
    intro w hw
    exact (positiveSmoothWindow_contDiff ρ R).comp ((contDiff_apply ℝ ℝ w).comp contDiff_fst)
  · apply contDiff_prod
    intro w hw
    exact (positiveSmoothWindow_contDiff (ρ^2) (R^2)).comp
      (complex_normSq_contDiff.comp ((contDiff_apply ℝ ℂ w).comp contDiff_snd))

theorem smoothRootWeight_nonneg (ρ R : ℝ) (x : mixedSpace K) : 0 ≤ smoothRootWeight ρ R x :=
  mul_nonneg (Finset.prod_nonneg (fun _ _ => positiveSmoothWindow_nonneg _ _ _))
    (Finset.prod_nonneg (fun _ _ => positiveSmoothWindow_nonneg _ _ _))

theorem smoothRootWeight_le_one (ρ R : ℝ) (x : mixedSpace K) : smoothRootWeight ρ R x ≤ 1 := by
  apply (mul_le_mul _ _ (Finset.prod_nonneg (fun _ _ => positiveSmoothWindow_nonneg _ _ _))
    zero_le_one).trans_eq (one_mul 1)
  · exact Finset.prod_le_one (fun _ _ => positiveSmoothWindow_nonneg _ _ _)
      (fun _ _ => positiveSmoothWindow_le_one _ _ _)
  · exact Finset.prod_le_one (fun _ _ => positiveSmoothWindow_nonneg _ _ _)
      (fun _ _ => positiveSmoothWindow_le_one _ _ _)

theorem smoothRootWeight_eq_one (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    {x : mixedSpace K} (hx : x ∈ rootBox K ρ R) : smoothRootWeight ρ R x = 1 := by
  have hr (w : {w : InfinitePlace K // IsReal w}) : positiveSmoothWindow ρ R (x.1 w) = 1 := by
    have h := hx.1 w
    rw [normAtPlace_apply_of_isReal w.property, Real.norm_eq_abs, abs_of_nonneg (hx.2 w)] at h
    exact positiveSmoothWindow_eq_one hρ hR h.1 h.2
  have hc (w : {w : InfinitePlace K // IsComplex w}) :
      positiveSmoothWindow (ρ^2) (R^2) (Complex.normSq (x.2 w)) = 1 := by
    have h := hx.1 w
    rw [normAtPlace_apply_of_isComplex w.property] at h
    apply positiveSmoothWindow_eq_one (sq_pos_of_pos hρ) (sq_pos_of_pos hR)
    · rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ hρ.le h.1 2
    · rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) h.2 2
  simp only [smoothRootWeight, hr, hc, Finset.prod_const_one, one_mul]

theorem smoothRootWeight_support_subset (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    Function.support (smoothRootWeight (K := K) ρ R) ⊆ rootBox K (ρ/2) (2*R) := by
  intro x hx
  have hh := mul_ne_zero_iff.mp hx
  have hr (w : {w : InfinitePlace K // IsReal w}) : ρ/2 < x.1 w ∧ x.1 w < 2*R :=
    positiveSmoothWindow_support hρ hR ((Finset.prod_ne_zero_iff.mp hh.1) w (Finset.mem_univ w))
  have hc (w : {w : InfinitePlace K // IsComplex w}) : ρ/2 < ‖x.2 w‖ ∧ ‖x.2 w‖ < 2*R := by
    have ht := positiveSmoothWindow_support (sq_pos_of_pos hρ) (sq_pos_of_pos hR)
      ((Finset.prod_ne_zero_iff.mp hh.2) w (Finset.mem_univ w))
    rw [Complex.normSq_eq_norm_sq] at ht
    constructor
    · by_contra hn
      have hn' : ‖x.2 w‖ ≤ ρ/2 := le_of_not_gt hn
      have hs := pow_le_pow_left₀ (norm_nonneg (x.2 w)) hn' 2
      nlinarith [sq_pos_of_pos hρ]
    · by_contra hn
      have hn' : 2*R ≤ ‖x.2 w‖ := le_of_not_gt hn
      have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*R) hn' 2
      nlinarith [sq_pos_of_pos hR]
  refine ⟨fun w => ?_, fun w => (hr w).1.le.trans' (by positivity)⟩
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_eq_abs,
      abs_of_pos (lt_trans (by positivity) (hr ⟨w, hw⟩).1)]
    exact ⟨(hr ⟨w, hw⟩).1.le, (hr ⟨w, hw⟩).2.le⟩
  · rw [normAtPlace_apply_of_isComplex hw]
    exact ⟨(hc ⟨w, hw⟩).1.le, (hc ⟨w, hw⟩).2.le⟩

theorem smoothRootWeight_hasCompactSupport (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) :
    HasCompactSupport (smoothRootWeight (K := K) ρ R) :=
  HasCompactSupport.of_support_subset_isCompact (rootBox_isCompact (K := K) (ρ/2) (2*R))
    (smoothRootWeight_support_subset ρ R hρ hR)

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.smoothRootWeight_eq_one
#print axioms WaringSiegel.WSL3.smoothRootWeight_contDiff
