import WaringSiegel.WSL2IdealSummability
import WaringSiegel.WSL2LocalEulerFactor
import WaringSiegel.WSL2LocalResidueNorm
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# WSL2: the actual cubic local-density Euler product

The ideal norm series, the actual completion-residue norm identity, and the
proved uniform good-prime density error supply convergence. Explicit positive
all-prime lower bounds give one product lower bound independent of the target.
-/

noncomputable section
open Filter Topology IsLocalRing
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField

namespace WaringSiegel

/-- A summable uniform tail and fixed positive exceptional lower bounds give
one strictly positive infinite-product lower bound for the entire family. -/
theorem uniform_positive_product_of_summable_errors {ι : Type*}
    (err lower : ι → ℝ) (herr : Summable err)
    (good : ι → Prop) (hgood : ∀ᶠ i in cofinite, good i)
    (hlower : ∀ i, 0 < lower i) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ι → ℝ, (∀ i, lower i ≤ σ i) →
      (∀ i, good i → |σ i - 1| ≤ err i) →
      Multipliable σ ∧ c ≤ ∏' i, σ i := by
  have hsmall : ∀ᶠ i in cofinite, err i < (1/2 : ℝ) :=
    herr.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  have hboth : ∀ᶠ i in cofinite, good i ∧ err i < (1/2 : ℝ) := hgood.and hsmall
  let b : ι → ℝ := fun i => if good i ∧ err i < (1/2 : ℝ) then 1 - err i else lower i
  have hb : ∀ i, 0 < b i := by
    intro i
    dsimp [b]
    split_ifs with h
    · linarith [h.2]
    · exact hlower i
  have hbsum : Summable (fun i => b i - 1) := by
    apply herr.neg.congr_cofinite
    filter_upwards [hboth] with i hi
    dsimp [b]
    rw [if_pos hi]
    ring
  have hblog : Summable (fun i => Real.log (b i)) := by
    convert Real.summable_log_one_add_of_summable hbsum using 1
    funext i
    congr 1
    ring
  refine ⟨Real.exp (∑' i, Real.log (b i)), Real.exp_pos _, ?_⟩
  intro σ hσlower hσerr
  have hσpos : ∀ i, 0 < σ i := fun i => (hlower i).trans_le (hσlower i)
  have hσsum : Summable (fun i => σ i - 1) := by
    apply herr.of_norm_bounded_eventually
    filter_upwards [hgood] with i hi
    simpa only [Real.norm_eq_abs] using hσerr i hi
  have hσlog : Summable (fun i => Real.log (σ i)) := by
    convert Real.summable_log_one_add_of_summable hσsum using 1
    funext i
    congr 1
    ring
  have hbσ : ∀ i, b i ≤ σ i := by
    intro i
    dsimp [b]
    split_ifs with h
    · have hle := (abs_le.mp (hσerr i h.1)).1
      linarith
    · exact hσlower i
  refine ⟨Real.multipliable_of_summable_log hσpos hσlog, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hσpos hσlog]
  exact Real.exp_le_exp.mpr
    (hblog.tsum_le_tsum (fun i => Real.log_le_log (hb i) (hbσ i)) hσlog)

variable {K : Type*} [Field K] [NumberField K]

theorem bad_cubic_residue_prime_divides_six
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : ResidueField (v.adicCompletionIntegers K)) = 0) :
    v.asIdeal ∣ Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K)) := by
  have hq : (6 : 𝓞 K ⧸ v.asIdeal) = 0 := by
    apply (quotientCompletionResidueEquiv v).injective
    simpa only [map_ofNat, map_zero] using h6
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using hq)

theorem good_cubic_residue_primes_cofinite :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in cofinite,
      (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 := by
  have hA : Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K)) ≠ 0 :=
    mt Ideal.span_singleton_eq_bot.mp (by norm_num)
  have hfinite := (IdealDivisorBounds.idealDivisors_finite _ hA).preimage
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v _ w _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
  apply Filter.mem_cofinite.mpr
  apply hfinite.subset
  intro v hv
  exact bad_cubic_residue_prime_divides_six v (by simpa only [Set.mem_compl_iff,
    Set.mem_setOf_eq, not_not] using hv)

def cubicEulerError (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  24 * (Ideal.absNorm v.asIdeal : ℝ)^(-(3/2 : ℝ))

theorem cubicEulerError_nonneg (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 ≤ cubicEulerError v := by unfold cubicEulerError; positivity

theorem cubicEulerError_summable :
    Summable (cubicEulerError (K := K)) :=
  (primeIdeal_norm_rpow_summable (K := K) (by norm_num : (1 : ℝ) < 3/2)).mul_left 24

theorem cubicEulerError_sq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    cubicEulerError v ^ 2 = 576 / (Ideal.absNorm v.asIdeal : ℝ)^3 := by
  have hq : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  unfold cubicEulerError
  rw [mul_pow, ← Real.rpow_mul_natCast hq.le]
  norm_num
  norm_num [Real.rpow_natCast, div_eq_mul_inv, inv_pow]
  norm_cast

/-- The actual convergent local densities have an absolutely convergent Euler
product bounded below by one positive field-dependent constant, chosen before
every eligible nonzero target. -/
theorem completion_cubic_euler_product_uniform_positive :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ completionCubicDensityLowerBound v ≤ σ v ∧
          Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
            (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 (σ v))) ∧
        Summable (fun v => |σ v - 1|) ∧ Multipliable σ ∧ c ≤ ∏' v, σ v := by
  obtain ⟨c, hc, hproduct⟩ := uniform_positive_product_of_summable_errors
    (cubicEulerError (K := K)) completionCubicDensityLowerBound
    cubicEulerError_summable
    (fun v => (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    good_cubic_residue_primes_cofinite completionCubicDensityLowerBound_pos
  refine ⟨c, hc, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ⟩ := completion_cubic_density_family_with_euler_tail hν hν0
  have herr : ∀ v, (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 →
      |σ v - 1| ≤ cubicEulerError v := by
    intro v h6
    apply abs_le_of_sq_le_sq _ (cubicEulerError_nonneg v)
    rw [cubicEulerError_sq]
    have hsq := (hσ v).2 h6
    rwa [completion_residue_card_eq_absNorm] at hsq
  have hsum : Summable (fun v => σ v - 1) := by
    apply cubicEulerError_summable.of_norm_bounded_eventually
    filter_upwards [good_cubic_residue_primes_cofinite (K := K)] with v hv
    simpa only [Real.norm_eq_abs] using herr v hv
  obtain ⟨hprod, hlower⟩ := hproduct σ (fun v => (hσ v).1.2.1) herr
  exact ⟨σ, fun v => (hσ v).1, by simpa only [Real.norm_eq_abs] using hsum.norm,
    hprod, hlower⟩

end WaringSiegel

#print axioms WaringSiegel.completion_cubic_euler_product_uniform_positive
