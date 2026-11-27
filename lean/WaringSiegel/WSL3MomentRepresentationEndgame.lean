import WaringSiegel.WSL3MomentRepresentationMajor
import WaringSiegel.WSL2UnitReduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exact remaining major-arc premise for the local-conditional target

This module does not prove that major-arc lower bound. It states it for the
literal integral, proves that it dominates the now-closed minor estimate
for all sufficiently large targets, and performs the actual compact-region
and positive-unit descent to the unchanged LocalConditionalBound target.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module Filter
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem positive_volume_saving_eventually_dominated
    (k : ℕ) (hk : 0<k) (C c η : ℝ) (hc : 0<c) (hη : 0<η) :
    ∃ N : ℝ, 0<N ∧ ∀ y : ℝ, N<y → ∀ a : ℝ,
      C*(y^(1/(k:ℝ)))^(a-η) < c*(y^(1/(k:ℝ)))^a := by
  have hkR : 0<(k:ℝ) := by exact_mod_cast hk
  have hev : ∀ᶠ y : ℝ in atTop, C/c<y^(η/(k:ℝ)) :=
    (tendsto_rpow_atTop (div_pos hη hkR)).eventually_gt_atTop (C/c)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨max 1 N,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro y hy a
  have hy0 : 0<y := lt_trans (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hy
  have hlarge := hN y ((le_max_right _ _).trans hy.le)
  have hid : (y^(1/(k:ℝ)))^η = y^(η/(k:ℝ)) := by
    rw [← Real.rpow_mul hy0.le]
    congr 1
    ring
  have hC : C<c*(y^(1/(k:ℝ)))^η := by
    rw [hid]
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hlarge
  have hX : 0<y^(1/(k:ℝ)) := Real.rpow_pos_of_pos hy0 _
  calc
    _ < (c*(y^(1/(k:ℝ)))^η)*(y^(1/(k:ℝ)))^(a-η) :=
      mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hX _)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hX]; congr 2 <;> ring

/-- The actual smooth major coefficient, with its original trace Haar
normalization and the same conductor cutoff used in the minor theorem. -/
def smoothRootMajorCoefficient
    (k s : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (target : 𝓞 K) (htarget : target≠0) : ℂ :=
  ∫ q in traceMajorArcUnion ((rootScale k target)^k)
    ((k:ℝ)^finrank ℚ K*(rootScale k target)^finrank ℚ K),
    (compactTraceWeylSum k (smoothWeightSchwartz ρ R hρ hR)
      (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
      (rootScale k target) (rootScale_pos htarget k).ne' q)^s *
      traceTorusCharacter (-target) q ∂traceHaar

/-- A remaining analytic assertion, not an established estimate. It is
restricted to the actual normalized compact target region and retains the
exact unit-coordinate local hypothesis. -/
def SmoothMajorLowerBound
    (k s : ℕ) (B ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) : Prop :=
  ∃ c N : ℝ, 0<c ∧ 0<N ∧ ∀ (target : 𝓞 K) (htarget : target≠0),
    TotallyPositive target → LocalUnitSolvable k s target → N<absNorm target →
    normalizedTarget k 1 target ∈ compactTargetSet K B →
      c*((rootScale k target)^finrank ℚ K : ℝ)^((s:ℝ)-k) ≤
        (smoothRootMajorCoefficient k s ρ R hρ hR target htarget).re

theorem compactLocalConditional_of_smoothRootMajor_lower
    (k s : ℕ) (hk : 3≤k) (hs : 0<s)
    (hvariables : Thresholds.sufficientVariables k ≤ (s:ℤ))
    (B ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (hmajor : SmoothMajorLowerBound (K := K) k s B ρ R hρ hR) :
    CompactLocalConditionalBound K k s B := by
  obtain ⟨C,η,hC,hη,hrepresent⟩ := representable_of_smoothRootMajor_dominance (K := K)
    k s hk hs hvariables ρ R hρ hR
  obtain ⟨c,N,hc,hN,hmain⟩ := hmajor
  obtain ⟨M,hM,hdom⟩ := positive_volume_saving_eventually_dominated k (by omega) C c η hc hη
  refine ⟨(2*R)^finrank ℚ K,by positivity,max N M,
    lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro target hpositive hlocal hsize hregion
  have htarget : target≠0 := by
    intro hz
    have hh := lt_trans (lt_of_lt_of_le hN (le_max_left N M)) hsize
    simpa [hz,absNorm] using hh
  apply hrepresent target htarget
  have hsmall := hdom (absNorm target) ((le_max_right _ _).trans_lt hsize) ((s:ℝ)-k)
  have hscaled : C*((rootScale k target)^finrank ℚ K : ℝ)^((s:ℝ)-k-η) <
      c*((rootScale k target)^finrank ℚ K : ℝ)^((s:ℝ)-k) := by
    simpa only [rootScale_pow_degree k (show 0<k by omega)] using hsmall
  exact hscaled.trans_le (hmain target htarget hpositive hlocal
    ((le_max_left _ _).trans_lt hsize) hregion)

/-- A single actual major-arc estimate on a fixed compact region suffices.
The minor estimate, positive-root extraction, norm height, and unit descent
are proved here and in its checked dependencies. -/
theorem exists_compact_smoothMajor_reduction
    (K : Type*) [Field K] [NumberField K] (k : ℕ) (hk : 3≤k) :
    ∃ B : ℝ, 1≤B ∧ IsCompact (compactTargetSet K B) ∧
      ∀ (s : ℕ) (hs : 0<s), Thresholds.sufficientVariables k ≤ (s:ℤ) →
      ∀ (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R),
        SmoothMajorLowerBound (K := K) k s B ρ R hρ hR → LocalConditionalBound K k s := by
  obtain ⟨B,hB,hcompact,hreduce⟩ := exists_compact_local_reduction K k (by omega)
  refine ⟨B,hB,hcompact,?_⟩
  intro s hs hvariables ρ R hρ hR hmajor
  apply (hreduce s).mp
  exact compactLocalConditional_of_smoothRootMajor_lower k s hk hs hvariables B ρ R hρ hR hmajor

#print axioms positive_volume_saving_eventually_dominated
#print axioms compactLocalConditional_of_smoothRootMajor_lower
#print axioms exists_compact_smoothMajor_reduction
end WaringSiegel.WSL3
