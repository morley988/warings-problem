import WaringSiegel.WSL2LongThinDualDecay

/-!
# WSL2: uniform summability of an actual dual Gaussian

The exponent is the sum of squared absolute values at real places and squared
complex moduli at complex places, hence a genuine positive quadratic form on
V×V. The series runs over the actual lattice pairs. Its bound follows from
the dual close-pair count; Gaussian Poisson summation is not asserted here.
-/

noncomputable section
set_option maxHeartbeats 1000000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def mixedSquareNorm (x : mixedSpace K) : ℝ := ∑ w, (normAtPlace w x)^2

theorem mixed_norm_sq_le_mixedSquareNorm (x : mixedSpace K) : ‖x‖^2 ≤ mixedSquareNorm x := by
  obtain ⟨w, hw, he⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (InfinitePlace K)).Nonempty) (fun w => normAtPlace w x)
  rw [norm_eq_sup'_normAtPlace, he]
  exact Finset.single_le_sum (fun v _ => sq_nonneg (normAtPlace v x)) hw

theorem gaussian_le_polynomial_decay (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    Real.exp (-r^2) ≤ Real.exp ((m:ℝ)^2/4)/(1+r)^m := by
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+r) m)).mpr
  calc
    _ ≤ Real.exp (-r^2)*(Real.exp r)^m := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp r]) m)
      (Real.exp_pos _).le
    _ = Real.exp (-r^2+(m:ℝ)*r) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (r-(m:ℝ)/2)])

def longThinDualGaussian (θ : mixedSpace K) (P H : ℝ) (p : 𝓞 K × K) : ℝ :=
  Real.exp (-(mixedSquareNorm (mixedEmbedding K (p.1:K))/P^2 +
    (P*H)^2*mixedSquareNorm (θ*mixedEmbedding K (p.1:K)-mixedEmbedding K p.2)))

def longThinGaussianFactor (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.exp (((5*finrank ℚ K+2:ℕ):ℝ)^2/4)

theorem longThinDualGaussian_le_decay (θ : mixedSpace K) (P H : ℝ)
    (hP : 0 < P) (hH : 0 ≤ H) (p : 𝓞 K × K) :
    longThinDualGaussian θ P H p ≤ longThinGaussianFactor K * longThinDualDecay θ P H p := by
  let y := mixedEmbedding K (p.1:K)
  let e := θ*y-mixedEmbedding K p.2
  let a := ‖y‖/P
  let b := (P*H)*‖e‖
  have ha : 0 ≤ a := div_nonneg (norm_nonneg _) hP.le
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg hP.le hH) (norm_nonneg _)
  have hya : a^2 ≤ mixedSquareNorm y/P^2 := by
    dsimp [a]
    rw [div_pow]
    exact div_le_div_of_nonneg_right (mixed_norm_sq_le_mixedSquareNorm y) (sq_nonneg P)
  have heb : b^2 ≤ (P*H)^2*mixedSquareNorm e := by
    dsimp [b]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (mixed_norm_sq_le_mixedSquareNorm e) (sq_nonneg _)
  have hmax : (max a b)^2 ≤ a^2+b^2 := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg a]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg b]
  have hrad : (longThinDualRadius θ P H p)^2 ≤
      mixedSquareNorm y/P^2+(P*H)^2*mixedSquareNorm e := by
    exact hmax.trans (add_le_add hya heb)
  calc
    _ ≤ Real.exp (-(longThinDualRadius θ P H p)^2) :=
      Real.exp_le_exp.mpr (neg_le_neg hrad)
    _ ≤ Real.exp (((5*finrank ℚ K+2:ℕ):ℝ)^2/4)/
        (1+longThinDualRadius θ P H p)^(5*finrank ℚ K+2) :=
      gaussian_le_polynomial_decay _ (longThinDualRadius_nonneg θ P H hP.le p) _
    _ = _ := by unfold longThinGaussianFactor longThinDualDecay; ring

/-- A true Gaussian on the actual dual lattice has a bound independent of
P,H and θ outside the conductor major arcs. -/
theorem longThinDualGaussian_summable_bound
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (θ : mixedSpace K) (P H : ℝ) (hP : 1 ≤ P) (hH : 1 ≤ H) (hPH : P ≤ H^2)
    (hminor : ∀ γ : K, P^finrank ℚ K <
      (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight (P^2*H) (θ-mixedEmbedding K γ)) :
    Summable (fun p : longThinDualDomain I => longThinDualGaussian θ P H p) ∧
      (∑' p : longThinDualDomain I, longThinDualGaussian θ P H p) ≤
        2*longThinGaussianFactor K*longThinDualConstant I := by
  obtain ⟨hs, hb⟩ := longThinDualDecay_summable_bound I hI θ P H hP hH hPH hminor
  have hC : 0 ≤ longThinGaussianFactor K := (Real.exp_pos _).le
  have hbound := fun p : longThinDualDomain I =>
    longThinDualGaussian_le_decay θ P H (by linarith) (by linarith) p
  have hsm := hs.mul_left (longThinGaussianFactor K)
  have hsg := Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hbound hsm
  refine ⟨hsg, (hsg.tsum_le_tsum hbound hsm).trans ?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (by ring)

end WaringSiegel
