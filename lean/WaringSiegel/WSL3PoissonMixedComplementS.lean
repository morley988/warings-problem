import WaringSiegel.WSL3PoissonMixedCauchy
import WaringSiegel.WSL3PoissonMixedJVolume

/-! # Cauchy reduction of the literal complementary S2 aggregate

The h=0 term is removed. The aggregate remains complex; its absolute
integral is bounded through genuine nonnegative I and J integrals.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def compactMixedSIntegrand (u w g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w)
    (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H P M R : ℝ) (hH : H ≠ 0) (hP : P ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (q : ArchimedeanTraceTorus K) : ℂ :=
  (∑ h : (compactIntegerSupport u huc H hH).erase 0,
    u (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K)) *
      compactTraceWeylSum 2 w hwc P hP (traceTorusMul (3*(h:𝓞 K)) q) *
      compactTraceWeylSum 6 g hgc M hM (traceTorusMul ((h:𝓞 K)^3) q)) *
        ((‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 : ℝ):ℂ)

def compactMixedSComplementIntegral (u w g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w)
    (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H P M R : ℝ) (hH : H ≠ 0) (hP : P ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0) : ℂ :=
  ∫ q in mixedComplementArcs P H, compactMixedSIntegrand u w g v huc hwc hgc hvc H P M R hH hP hM hR q ∂traceHaar

/-- Actual nonnegative J, for an actual nonnegative smooth h-weight. -/
theorem compactMixedJIntegral_norm_eq_real (u g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H M R : ℝ) (hH : H ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (hu : ∀ x, u x = (‖u x‖:ℂ)) :
    ‖compactMixedJIntegral u g v huc hgc hvc H M R hH hM hR‖ =
      ∫ q, (∑ h : (compactIntegerSupport u huc H hH).erase 0,
        ‖u (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K))‖ *
          ‖compactTraceWeylSum 6 g hgc M hM (traceTorusMul ((h:𝓞 K)^3) q)‖^2) *
        ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 ∂traceHaar := by
  let f : ArchimedeanTraceTorus K → ℝ := fun q =>
    (∑ h : (compactIntegerSupport u huc H hH).erase 0,
      ‖u (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K))‖ *
        ‖compactTraceWeylSum 6 g hgc M hM (traceTorusMul ((h:𝓞 K)^3) q)‖^2) *
      ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4
  have hfun (q : ArchimedeanTraceTorus K) :
      compactMixedJIntegrand u g v huc hgc hvc H M R hH hM hR q = (f q:ℂ) := by
    unfold compactMixedJIntegrand
    rw [← Finset.sum_coe_sort ((compactIntegerSupport u huc H hH).erase 0)]
    simp only [f,Complex.ofReal_mul,Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    exact congrArg (fun z : ℂ => z *
      ((‖compactTraceWeylSum 6 g hgc M hM (traceTorusMul ((h:𝓞 K)^3) q)‖^2:ℝ):ℂ)) (hu _)
  have he : compactMixedJIntegral u g v huc hgc hvc H M R hH hM hR = (((∫ q, f q ∂traceHaar):ℝ):ℂ) := by
    unfold compactMixedJIntegral
    simp_rw [hfun]
    exact integral_complex_ofReal
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  exact integral_nonneg (fun q => mul_nonneg
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))
    (pow_nonneg (norm_nonneg _) _))

/-- The actual complementary aggregate satisfies |S2|^2 <= W I J. -/
theorem compactMixedSComplementIntegral_cauchy (u w g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w)
    (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H P M R : ℝ) (hH : 0 < H) (hP : 0 < P) (hM : M ≠ 0) (hR : R ≠ 0)
    (hu : ∀ x, u x = (‖u x‖:ℂ)) (W : ℝ) (hW : 0 ≤ W) (huW : ∀ x, ‖u x‖ ≤ W) :
    ‖compactMixedSComplementIntegral u w g v huc hwc hgc hvc H P M R hH.ne' hP.ne' hM hR‖^2 ≤
      W*mixedComplementIntegral w v hwc hvc P H R hP.ne' hR
        ((compactIntegerSupport u huc H hH.ne').erase 0) *
      ‖compactMixedJIntegral u g v huc hgc hvc H M R hH.ne' hM hR‖ := by
  let U := (compactIntegerSupport u huc H hH.ne').erase 0
  let a : U → ℝ := fun h => ‖u (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K))‖
  let F : U → ArchimedeanTraceTorus K → ℂ := fun h q =>
    compactTraceWeylSum 2 w hwc P hP.ne' (traceTorusMul (3*(h:𝓞 K)) q)
  let G : U → ArchimedeanTraceTorus K → ℂ := fun h q =>
    compactTraceWeylSum 6 g hgc M hM (traceTorusMul ((h:𝓞 K)^3) q)
  let V : ArchimedeanTraceTorus K → ℝ := fun q =>
    ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4
  have ha (h : U) : 0 ≤ a h := norm_nonneg _
  have hF (h : U) : Continuous (F h) :=
    (compactTraceWeylSum_continuous _ _ _ _ _).comp (traceTorusMul_continuous _)
  have hG (h : U) : Continuous (G h) :=
    (compactTraceWeylSum_continuous _ _ _ _ _).comp (traceTorusMul_continuous _)
  have hV : Continuous V :=
    ((compactTraceWeylSum_continuous _ _ _ _ _).comp (traceTorusMul_continuous _)).norm.pow 4
  have hV0 (q : ArchimedeanTraceTorus K) : 0 ≤ V q := pow_nonneg (norm_nonneg _) _
  let S := mixedComplementArcs (K:=K) P H
  let A : ArchimedeanTraceTorus K → ℝ := fun q => (∑ h : U, a h*‖F h q‖^2)*V q
  let B : ArchimedeanTraceTorus K → ℝ := fun q => (∑ h : U, a h*‖G h q‖^2)*V q
  have hA : Continuous A :=
    (continuous_finset_sum _ (fun h _ => continuous_const.mul ((hF h).norm.pow 2))).mul hV
  have hB : Continuous B :=
    (continuous_finset_sum _ (fun h _ => continuous_const.mul ((hG h).norm.pow 2))).mul hV
  have hB0 (q : ArchimedeanTraceTorus K) : 0 ≤ B q := mul_nonneg
    (Finset.sum_nonneg (fun h _ => mul_nonneg (ha h) (sq_nonneg _))) (hV0 q)
  have hcs := compact_weighted_sum_integral_cauchy (μ:=traceHaar.restrict S) a ha F G hF hG V hV hV0
  have heS : (∫ q in S, (∑ h : U, (a h:ℂ)*F h q*G h q)*(V q:ℂ) ∂traceHaar) =
      compactMixedSComplementIntegral u w g v huc hwc hgc hvc H P M R hH.ne' hP.ne' hM hR := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by simp only [a,F,G,V,U,compactMixedSIntegrand,← hu] <;> rfl)
  rw [heS] at hcs
  have hJ : (∫ q in S, B q ∂traceHaar) ≤
      ‖compactMixedJIntegral u g v huc hgc hvc H M R hH.ne' hM hR‖ := by
    rw [compactMixedJIntegral_norm_eq_real _ _ _ _ _ _ _ _ _ _ _ _ hu]
    exact setIntegral_le_integral
      (hB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall hB0)
  have hI : (∫ q in S, A q ∂traceHaar) ≤
      W*mixedComplementIntegral w v hwc hvc P H R hP.ne' hR U := by
    let C : ArchimedeanTraceTorus K → ℝ := fun q => compactTraceQuadraticAverage w hwc P hP.ne' U q*V q
    have hC : Continuous C := (compactTraceQuadraticAverage_continuous _ _ _ _ _).mul hV
    calc
      _ ≤ ∫ q in S, W*C q ∂traceHaar := by
        apply integral_mono
          (hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          ((continuous_const.mul hC).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        intro q
        dsimp [A,C]
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (hV0 q)
        rw [compactTraceQuadraticAverage,← Finset.sum_coe_sort U,Finset.mul_sum]
        exact Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_right (huW _) (sq_nonneg _))
      _ = _ := integral_const_mul _ _
  apply hcs.trans
  exact mul_le_mul hI hJ (integral_nonneg hB0)
    (mul_nonneg hW (mixedComplementIntegral_nonneg _ _ _ _ _ _ _ _ _ _))

end WaringSiegel.WSL3Poisson
