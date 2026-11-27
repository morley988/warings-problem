import WaringSiegel.WSL4MajorQuadraticAverage
import WaringSiegel.WSL4MajorFlexibleScale
import WaringSiegel.WSL3MomentRepresentationMajor
import WaringSiegel.WSL4MajorSources

/-! # A genuine quadratic shrinking-minor saving at 256 variables -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem quadratic_translation_window (P : ℝ) (hP : 1≤P) :
    1≤P^((2:ℝ)/3) ∧ P^((2:ℝ)/3)≤P ∧
      (P^((2:ℝ)/3))^2≤P^2/P^((2:ℝ)/3) ∧ P≤P^2/P^((2:ℝ)/3) := by
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hB0 : 0<P^((2:ℝ)/3) := Real.rpow_pos_of_pos hP0 _
  have hB : P^((2:ℝ)/3)≤P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (2:ℝ)/3≤1)
  refine ⟨Real.one_le_rpow hP (by norm_num),hB,?_,?_⟩
  · apply (le_div_iff₀ hB0).mpr
    have he : (P^((2:ℝ)/3))^3=P^2 := by
      rw [← Real.rpow_mul_natCast hP0.le]
      norm_num
    exact le_of_eq ((by ring : (P^((2:ℝ)/3))^2*P^((2:ℝ)/3)=(P^((2:ℝ)/3))^3).trans he)
  · apply (le_div_iff₀ hB0).mpr
    exact (mul_le_mul_of_nonneg_left hB hP0.le).trans_eq (by ring)

theorem compactTraceQuadraticSum_shrinking_square
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ)) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 1≤P), ∀ q∈shrinkingMinorArcs (K := K) 2 (2/3) P,
      ‖compactTraceWeylSum 2 f hc P (by linarith) q‖^2 ≤ C*(P^finrank ℚ K)^((5:ℝ)/3) := by
  obtain ⟨C,hC,hb⟩ := compactTraceQuadraticSum_flexible_bound f hc
  refine ⟨C,hC,?_⟩
  intro P hP q hq
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  obtain ⟨hB,hBP,hBH,hPH⟩ := quadratic_translation_window P hP
  rw [shrinkingMinorArcs_eq_flexible _ _ _ hP0] at hq
  have hh := hb P (P^((2:ℝ)/3)) (P^2/P^((2:ℝ)/3)) hP hB hBP hBH hPH q hq
  have he := flexible_volume_scale P hP0 (finrank ℚ K) 0 2 ((2:ℝ)/3) 1
  norm_num only [pow_zero,one_mul,Real.rpow_one,Nat.cast_zero,Nat.cast_ofNat] at he
  norm_num only at he
  apply hh.trans_eq
  calc
    _ = C*((P^2/P^((2:ℝ)/3))^finrank ℚ K/(P^((2:ℝ)/3))^finrank ℚ K*(P^finrank ℚ K)) := by ring
    _ = _ := by rw [he]

theorem compactTraceQuadraticSum_shrinking_moment_256
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ)) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) 2 (2/3) P,
        ‖compactTraceWeylSum 2 f hc P (by linarith) q‖^256 ∂traceHaar) ≤
        C*(P^finrank ℚ K)^((253:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := compactTraceQuadraticSum_shrinking_square f hc
  refine ⟨C^128,by positivity,?_⟩
  intro P hP
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  let X := P^finrank ℚ K
  have hX1 : 1≤X := one_le_pow₀ hP
  have hX : 0<X := lt_of_lt_of_le zero_lt_one hX1
  have hpoint : ∀ q∈shrinkingMinorArcs (K := K) 2 (2/3) P,
      ‖compactTraceWeylSum 2 f hc P hP0.ne' q‖^256≤C^128*X^((253:ℝ)) := by
    intro q hq
    have hh := pow_le_pow_left₀ (sq_nonneg _) (hb P hP q hq) 128
    rw [← pow_mul,mul_pow,← Real.rpow_mul_natCast hX.le] at hh
    norm_num only [Nat.reduceMul,Nat.cast_ofNat] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by positivity))
  have hi : Integrable (fun q => ‖compactTraceWeylSum 2 f hc P hP0.ne' q‖^256) traceHaar :=
    ((compactTraceWeylSum_continuous _ _ _ _ _).norm.pow 256).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ q in shrinkingMinorArcs (K := K) 2 (2/3) P,C^128*X^((253:ℝ)) ∂traceHaar :=
      setIntegral_mono_on hi.integrableOn (integrable_const _).integrableOn
        (shrinkingMinorArcs_measurable _ _ _ hP0) hpoint
    _ ≤ ∫ q : ArchimedeanTraceTorus K,C^128*X^((253:ℝ)) ∂traceHaar :=
      setIntegral_le_integral (integrable_const _) (Filter.Eventually.of_forall (fun _ => by positivity))
    _ = _ := by simp [X]

theorem quadratic_smooth_full_sub_cutoff_bound (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (target : 𝓞 K) (htarget : target≠0),
      ‖(∫ q, smoothTraceSource 2 ρ R hρ hR (rootScale 2 target) (rootScale_pos htarget 2).ne' q^256 *
          traceTorusCharacter (-target) q ∂traceHaar) -
        (∫ q in traceMajorArcUnion ((rootScale 2 target)^2)
          ((2:ℝ)^finrank ℚ K*((rootScale 2 target)^finrank ℚ K)^((2:ℝ)/3)),
          smoothTraceSource 2 ρ R hρ hR (rootScale 2 target) (rootScale_pos htarget 2).ne' q^256 *
            traceTorusCharacter (-target) q ∂traceHaar)‖ ≤
        C*((rootScale 2 target)^finrank ℚ K)^((253:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := compactTraceQuadraticSum_shrinking_moment_256
    (smoothWeightSchwartz (K := K) ρ R hρ hR) (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
  refine ⟨C,hC,?_⟩
  intro target htarget
  let P := rootScale 2 target
  have hP0 : 0<P := rootScale_pos htarget 2
  let g : ArchimedeanTraceTorus K → ℂ := fun q => smoothTraceSource 2 ρ R hρ hR P hP0.ne' q^256 *
    traceTorusCharacter (-target) q
  have hg : Continuous g := ((compactTraceWeylSum_continuous _ _ _ _ _).pow 256).mul
    (traceTorusCharacter_continuous _)
  have hi : Integrable g traceHaar := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := integral_add_compl
    (traceMajorArcUnion_measurableSet (K := K) (P^2)
      ((2:ℝ)^finrank ℚ K*(P^finrank ℚ K)^((2:ℝ)/3)) (pow_pos hP0 2)) hi
  change ‖(∫ q,g q ∂traceHaar)-(∫ q in _,g q ∂traceHaar)‖≤_
  rw [← hs,add_sub_cancel_left]
  apply (norm_integral_le_integral_norm _).trans
  simpa only [g,smoothTraceSource,norm_mul,norm_pow,traceTorusCharacter,
    norm_latticeCharacter_eq_one,mul_one] using hb P (one_le_rootScale htarget 2)

#print axioms compactTraceQuadraticSum_shrinking_square
#print axioms compactTraceQuadraticSum_shrinking_moment_256
#print axioms quadratic_smooth_full_sub_cutoff_bound
end WaringSiegel.WSL4
