import WaringSiegel.WSL2IdealDivisors
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# WSL2: summability of actual ideal norms

An ideal of norm n divides the principal ideal (n). The proved ideal-divisor
epsilon estimate therefore bounds each norm fiber by C n^epsilon. Summing
these finite fibers proves absolute convergence for every real exponent > 1.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField WaringSiegel.IdealDivisorBounds

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem ideal_absNorm_span_nat (n : ℕ) :
    Ideal.absNorm (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) = n ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have hn : (n : 𝓞 K) = algebraMap ℤ (𝓞 K) (n : ℤ) := by simp
  rw [hn, Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis K),
    Int.natAbs_pow, Int.natAbs_natCast,
    ← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
    NumberField.RingOfIntegers.rank]

/-- The actual number of integral ideals of norm n has arbitrary epsilon growth. -/
theorem ideal_norm_fiber_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) ≤ C * (n : ℝ)^ε := by
  let d : ℝ := Module.finrank ℚ K
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  obtain ⟨C, hC, hbound⟩ := ideal_divisor_finset_bound (K := K) (div_pos hε hd)
  refine ⟨C, hC, ?_⟩
  intro n hn
  let S := (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset
  have hA : Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) ≠ 0 := by
    exact mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hn)
  have hdiv : ∀ I ∈ S, I ∣ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) := by
    intro I hI
    have hnorm : Ideal.absNorm I = n :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).mem_toFinset.mp hI
    rw [Ideal.dvd_iff_le, ← hnorm]
    exact Ideal.span_singleton_absNorm_le I
  have h := hbound _ hA S hdiv
  rw [ideal_absNorm_span_nat, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)] at h
  have hexp : (Module.finrank ℚ K : ℝ) * (ε / d) = ε := by dsimp [d] at *; field_simp
  rw [hexp] at h
  have hc : S.card = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
    exact (Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n)).symm
  rwa [hc] at h

theorem ideal_norm_fiber_series_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ)^(-s)) := by
  let δ : ℝ := (s - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, hbound⟩ := ideal_norm_fiber_bound (K := K) hδ
  have hexp : δ - s < -1 := by dsimp [δ]; linarith
  have hseries : Summable (fun n : ℕ => C * (n : ℝ)^(δ-s)) :=
    (Real.summable_nat_rpow.mpr hexp).mul_left C
  apply hseries.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · subst n
      have hs0 : -s ≠ 0 := by linarith
      have he0 : δ-s ≠ 0 := by linarith
      simp only [Nat.cast_zero, Real.zero_rpow hs0, Real.zero_rpow he0, mul_zero, le_refl]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      calc
        _ ≤ (C * (n : ℝ)^δ) * (n : ℝ)^(-s) :=
          mul_le_mul_of_nonneg_right (hbound n hn) (Real.rpow_nonneg hnpos.le _)
        _ = C * (n : ℝ)^(δ-s) := by
          rw [mul_assoc, ← Real.rpow_add hnpos]
          congr 2

/-- The actual integral-ideal norm series converges for every s > 1. The
zero ideal contributes zero under the standard real-power convention. -/
theorem ideal_norm_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ)^(-s)) := by
  let f : Ideal (𝓞 K) → ℕ := Ideal.absNorm
  letI (n : ℕ) : Fintype {I : Ideal (𝓞 K) // f I = n} :=
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).fintype
  rw [← (Equiv.sigmaFiberEquiv f).summable_iff]
  apply (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)).mpr
  constructor
  · intro n
    exact Summable.of_finite
  · have heq (n : ℕ) :
        (∑' I : {I : Ideal (𝓞 K) // f I = n},
          (Ideal.absNorm ((Equiv.sigmaFiberEquiv f) ⟨n,I⟩) : ℝ)^(-s)) =
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ)^(-s) := by
      simp only [Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, tsum_fintype]
      have hterm (I : {I : Ideal (𝓞 K) // f I = n}) : Ideal.absNorm I.val = n := I.property
      simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Nat.card_eq_fintype_card]
    simp_rw [heq]
    exact ideal_norm_fiber_series_summable hs

theorem primeIdeal_norm_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal : ℝ)^(-s)) := by
  apply (ideal_norm_rpow_summable (K := K) hs).comp_injective
  intro v w h
  exact IsDedekindDomain.HeightOneSpectrum.ext h

end WaringSiegel
