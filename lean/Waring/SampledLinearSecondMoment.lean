import Waring.QuadraticHeight

/-!
# Sampled linear Weyl sums: an actual second-moment estimate

Finite pair expansion, the sharp geometric-sum bound, and a symmetric
row-sum estimate give the large-sieve shape used by the coefficient sampling
argument. The coefficients are arbitrary complex numbers.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.SampledLinearSecondMoment

open QuadraticModulation

def sampledSecondMoment (β : ℝ) (N J : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range J, ‖∑ n ∈ Finset.range N, c n * e (β*(j : ℝ)*n)‖^2

def coefficientEnergy (N : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range N, ‖c n‖^2

/-- The elementary symmetric row-sum bound, proved by `2xy≤x²+y²`. -/
theorem symmetric_row_sum_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (K : ι → ι → ℝ) (B : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, K i j) ≤ B) :
    (∑ i ∈ s, ∑ j ∈ s, x i*x j*K i j) ≤ B*∑ i ∈ s, (x i)^2 := by
  have hpoint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      2*(x i*x j*K i j) ≤ ((x i)^2+(x j)^2)*K i j := by
    have h := mul_le_mul_of_nonneg_right
      (show 2*x i*x j ≤ (x i)^2+(x j)^2 by nlinarith [sq_nonneg (x i-x j)])
      (hK i hi j hj)
    nlinarith
  have hsum := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
  have hswap : (∑ i ∈ s, ∑ j ∈ s, (x j)^2*K i j) =
      ∑ i ∈ s, ∑ j ∈ s, (x i)^2*K i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have hbound : (∑ i ∈ s, ∑ j ∈ s, (x i)^2*K i j) ≤
      B*∑ i ∈ s, (x i)^2 := by
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ i ∈ s, (x i)^2*B :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; ring
  simp_rw [add_mul, Finset.sum_add_distrib] at hsum
  rw [hswap] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  simp_rw [← Finset.mul_sum] at hbound
  linarith

private theorem weighted_phase_pair (β : ℝ) (j m n : ℕ) (c : ℕ → ℂ) :
    (c m*e (β*(j : ℝ)*m))*conj (c n*e (β*(j : ℝ)*n)) =
      (c m*conj (c n))*e (β*((m : ℝ)-n)*j) := by
  rw [map_mul]
  calc
    _ = (c m*conj (c n))*(e (β*(j : ℝ)*m)*conj (e (β*(j : ℝ)*n))) := by ring
    _ = _ := by rw [e_mul_conj]; congr 2; ring

/-- Exact coefficient-pair expansion after summation over sampled phases. -/
theorem sampledSecondMoment_pair_identity (β : ℝ) (N J : ℕ) (c : ℕ → ℂ) :
    (sampledSecondMoment β N J c : ℂ) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        (c m*conj (c n))*∑ j ∈ Finset.range J, e (β*((m : ℝ)-n)*j) := by
  unfold sampledSecondMoment
  rw [Complex.ofReal_sum]
  simp_rw [norm_sq_eq_pair_sum, Finset.sum_product, weighted_phase_pair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.mul_sum]

/-- Every row of the reciprocal kernel is bounded by the full symmetric
shift interval and hence by twice its nonnegative half. -/
theorem reciprocal_kernel_row_bound (β : ℝ) (N J : ℕ) (hN : 0 < N)
    (m : ℕ) (hm : m < N) :
    (∑ n ∈ Finset.range N, linearSumBound J (β*((m : ℝ)-n))) ≤
      2*∑ h ∈ Finset.range N, linearSumBound J (β*(h : ℝ)) := by
  let f : ℤ → ℝ := fun u => linearSumBound J (β*(u : ℝ))
  let s := (Finset.range N).image (fun n : ℕ => (m : ℤ)-(n : ℤ))
  have hid : (∑ n ∈ Finset.range N, linearSumBound J (β*((m : ℝ)-n))) =
      ∑ u ∈ s, f u := by
    rw [Finset.sum_image]
    · simp only [f, Int.cast_sub, Int.cast_natCast]
    · intro i _ j _ hij
      dsimp at hij
      have hh : (i : ℤ) = (j : ℤ) := by omega
      exact_mod_cast hh
  have hsub : s ⊆ Finset.Icc (-((N-1 : ℕ) : ℤ)) ((N-1 : ℕ) : ℤ) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨n, hn, rfl⟩
    have hn' := Finset.mem_range.mp hn
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  rw [hid]
  have h := QuadraticHeight.symmetric_sum_le_twice (N-1) f
    (fun u => linearSumBound_nonneg _ _)
    (fun u => by simp only [f, Int.cast_neg, mul_neg, QuadraticHeight.linearSumBound_neg])
  have hNid : N-1+1=N := by omega
  rw [hNid] at h
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun u _ _ => linearSumBound_nonneg _ _)).trans
    (by simpa only [f, Int.cast_natCast] using h)

theorem coefficientEnergy_nonneg (N : ℕ) (c : ℕ → ℂ) : 0 ≤ coefficientEnergy N c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sampledSecondMoment_nonneg (β : ℝ) (N J : ℕ) (c : ℕ → ℂ) :
    0 ≤ sampledSecondMoment β N J c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem norm_linear_range_le (α : ℝ) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, e (α*(j : ℝ))‖ ≤ linearSumBound J α := by
  simpa only [e, Int.cast_zero, add_zero] using norm_exp_linear_sum_le 0 J α

/-- The exact sampled sums are controlled by the reciprocal kernel and the
coefficient energy. This is the finite large-sieve argument, not an assumed
large-sieve estimate. -/
theorem sampledSecondMoment_reciprocal_bound (β : ℝ) (N J : ℕ) (c : ℕ → ℂ)
    (hN : 0 < N) :
    sampledSecondMoment β N J c ≤
      (2*∑ h ∈ Finset.range N, linearSumBound J (β*(h : ℝ)))*coefficientEnergy N c := by
  let K : ℕ → ℕ → ℝ := fun m n => linearSumBound J (β*((m : ℝ)-n))
  have hpair : sampledSecondMoment β N J c ≤
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖c m‖*‖c n‖*K m n := by
    calc
      sampledSecondMoment β N J c = ‖(sampledSecondMoment β N J c : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sampledSecondMoment_nonneg _ _ _ _)]
      _ = ‖∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (c m*conj (c n))*∑ j ∈ Finset.range J, e (β*((m : ℝ)-n)*j)‖ := by
        rw [sampledSecondMoment_pair_identity]
      _ ≤ ∑ m ∈ Finset.range N, ‖∑ n ∈ Finset.range N,
          (c m*conj (c n))*∑ j ∈ Finset.range J, e (β*((m : ℝ)-n)*j)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          ‖(c m*conj (c n))*∑ j ∈ Finset.range J, e (β*((m : ℝ)-n)*j)‖ :=
        Finset.sum_le_sum (fun m _ => norm_sum_le _ _)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m _hm
        apply Finset.sum_le_sum
        intro n _hn
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (norm_linear_range_le _ _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply hpair.trans
  apply symmetric_row_sum_bound
  · intro m _ n _
    exact linearSumBound_nonneg _ _
  · intro m _ n _
    dsimp [K]
    have heq : β*((n : ℝ)-m) = -(β*((m : ℝ)-n)) := by ring
    rw [heq, QuadraticHeight.linearSumBound_neg]
  · intro m hm
    exact reciprocal_kernel_row_bound β N J hN m (Finset.mem_range.mp hm)

/-- Genuine intrinsic-height sampled second moment, in the denominator-error
large-sieve shape `NJ/L + N + J + L`, with an explicit logarithmic depth. -/
theorem sampledSecondMoment_intrinsic (β : ℝ) (N J T : ℕ) (c : ℕ → ℂ)
    (hN : 0 < N) (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2^T) :
    sampledSecondMoment β N J c ≤
      256 * ((N : ℝ)*J/RationalHeight.height ((N : ℝ)*J) β+
        N+J+RationalHeight.height ((N : ℝ)*J) β) * (T+1 : ℕ) * coefficientEnergy N c := by
  have h := ReciprocalSums.linearSumBound_sum_intrinsic β N J T hN hJ hJT
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  have he := mul_le_mul_of_nonneg_right hm (coefficientEnergy_nonneg N c)
  apply (sampledSecondMoment_reciprocal_bound β N J c hN).trans
  convert he using 1
  ring

/-- Canonical logarithmic-depth version, with no auxiliary depth premise. -/
theorem sampledSecondMoment_intrinsic_log (β : ℝ) (N J : ℕ) (c : ℕ → ℂ)
    (hN : 0 < N) (hJ : 0 < J) :
    sampledSecondMoment β N J c ≤
      256 * ((N : ℝ)*J/RationalHeight.height ((N : ℝ)*J) β+
        N+J+RationalHeight.height ((N : ℝ)*J) β) *
        (Nat.clog 2 J+1 : ℕ) * coefficientEnergy N c := by
  apply sampledSecondMoment_intrinsic β N J (Nat.clog 2 J) c hN hJ
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) J

/-- An arbitrary real shift of the sampling progression can be absorbed
into the coefficients without changing their energy. -/
theorem sampledSecondMoment_shifted_intrinsic (β σ : ℝ) (N J T : ℕ) (c : ℕ → ℂ)
    (hN : 0 < N) (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2^T) :
    (∑ j ∈ Finset.range J,
      ‖∑ n ∈ Finset.range N, c n*e (β*((j : ℝ)+σ)*n)‖^2) ≤
      256 * ((N : ℝ)*J/RationalHeight.height ((N : ℝ)*J) β+
        N+J+RationalHeight.height ((N : ℝ)*J) β) * (T+1 : ℕ) * coefficientEnergy N c := by
  let d : ℕ → ℂ := fun n => c n*e (β*σ*n)
  have henergy : coefficientEnergy N d = coefficientEnergy N c := by
    simp only [coefficientEnergy, d, norm_mul, norm_e, mul_one]
  have hphase (j n : ℕ) :
      c n*e (β*((j : ℝ)+σ)*n) = d n*e (β*(j : ℝ)*n) := by
    have heq : β*((j : ℝ)+σ)*n = β*σ*n+β*(j : ℝ)*n := by ring
    rw [heq, e_add]
    simp only [d, mul_assoc]
  simp_rw [hphase]
  have h := sampledSecondMoment_intrinsic β N J T d hN hJ hJT
  rw [henergy] at h
  exact h

/-- The logarithmic loss can be expressed directly with the real logarithm. -/
theorem sampledSecondMoment_intrinsic_real_log (β : ℝ) (N J : ℕ) (c : ℕ → ℂ)
    (hN : 0 < N) (hJ : 0 < J) :
    sampledSecondMoment β N J c ≤
      256 * ((N : ℝ)*J/RationalHeight.height ((N : ℝ)*J) β+
        N+J+RationalHeight.height ((N : ℝ)*J) β) *
        (2+Real.log (J : ℝ)/Real.log 2) * coefficientEnergy N c := by
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  obtain ⟨T, hcover, hcover2⟩ := ShortHeightDistribution.exists_dyadic_cover
    (a := 1) (P := (J : ℝ)) zero_lt_one hJ1
  have hJT : (J : ℝ) ≤ 2^T := by simpa only [one_mul] using hcover
  have hdepth := ShortHeightDistribution.dyadic_depth_le_log T (by norm_num : (1 : ℝ) ≤ 1)
    hJpos hcover2
  have hL : 0 < RationalHeight.height ((N : ℝ)*J) β := RationalHeight.height_pos _ _
  apply (sampledSecondMoment_intrinsic β N J T c hN hJ hJT).trans
  apply mul_le_mul_of_nonneg_right _ (coefficientEnergy_nonneg N c)
  apply mul_le_mul_of_nonneg_left hdepth
  positivity

/-- Arbitrarily translated sampling with the auxiliary dyadic depth removed. -/
theorem sampledSecondMoment_shifted_intrinsic_real_log
    (β σ : ℝ) (N J : ℕ) (c : ℕ → ℂ) (hN : 0 < N) (hJ : 0 < J) :
    (∑ j ∈ Finset.range J,
      ‖∑ n ∈ Finset.range N, c n*e (β*((j : ℝ)+σ)*n)‖^2) ≤
      256 * ((N : ℝ)*J/RationalHeight.height ((N : ℝ)*J) β+
        N+J+RationalHeight.height ((N : ℝ)*J) β) *
        (2+Real.log (J : ℝ)/Real.log 2) * coefficientEnergy N c := by
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  obtain ⟨T, hcover, hcover2⟩ := ShortHeightDistribution.exists_dyadic_cover
    (a := 1) (P := (J : ℝ)) zero_lt_one hJ1
  have hJT : (J : ℝ) ≤ 2^T := by simpa only [one_mul] using hcover
  have hdepth := ShortHeightDistribution.dyadic_depth_le_log T (by norm_num : (1 : ℝ) ≤ 1)
    hJpos hcover2
  have hL : 0 < RationalHeight.height ((N : ℝ)*J) β := RationalHeight.height_pos _ _
  apply (sampledSecondMoment_shifted_intrinsic β σ N J T c hN hJ hJT).trans
  apply mul_le_mul_of_nonneg_right _ (coefficientEnergy_nonneg N c)
  apply mul_le_mul_of_nonneg_left hdepth
  positivity

#print axioms sampledSecondMoment_pair_identity
#print axioms sampledSecondMoment_reciprocal_bound
#print axioms sampledSecondMoment_intrinsic
#print axioms sampledSecondMoment_shifted_intrinsic_real_log

end Waring.SampledLinearSecondMoment
