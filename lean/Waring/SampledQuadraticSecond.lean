import Waring.QuadraticHeight
import Waring.DifferenceSquaresFibers

/-!
# Sampled quadratic second moments with a common modulation

The linear phase is common to all sampled values. After expansion it is a
unit-modulus factor independent of the sample index. Difference-of-squares
fibers, rather than the pointwise fourth-power estimate, control the remaining
sum. This retains the full centered integer summation set.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.SampledQuadraticSecond
open QuadraticModulation

def squareDifference (p : ℤ × ℤ) : ℤ := p.1^2-p.2^2

def differenceFiber (S : Finset ℤ) (n : ℤ) : Finset (ℤ × ℤ) :=
  (S ×ˢ S).filter (fun p => squareDifference p = n)

def sampledMoment (S : Finset ℤ) (α t : ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H,
    ‖∑ z ∈ S, e (α*((h : ℝ)+1)*(z : ℝ)^2+t*z)‖^2

private theorem quadratic_phase_pair (α t : ℝ) (h : ℕ) (z w : ℤ) :
    e (α*((h : ℝ)+1)*(z : ℝ)^2+t*z)*
      conj (e (α*((h : ℝ)+1)*(w : ℝ)^2+t*w)) =
      e (t*((z : ℝ)-w))*
        e (α*((squareDifference (z,w) : ℤ) : ℝ)*((h : ℝ)+1)) := by
  rw [e_mul_conj, ← e_add]
  congr 1
  simp only [squareDifference, Int.cast_sub, Int.cast_pow]
  ring

/-- Exact expansion before taking absolute values. Common modulation is
what makes the first factor independent of the sample index. -/
theorem sampledMoment_pair_identity (S : Finset ℤ) (α t : ℝ) (H : ℕ) :
    (sampledMoment S α t H : ℂ) =
      ∑ p ∈ S ×ˢ S, e (t*((p.1 : ℝ)-p.2))*
        ∑ h ∈ Finset.range H, e (α*(squareDifference p : ℝ)*((h : ℝ)+1)) := by
  unfold sampledMoment
  rw [Complex.ofReal_sum]
  simp_rw [norm_sq_eq_pair_sum, quadratic_phase_pair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]

theorem sampledMoment_nonneg (S : Finset ℤ) (α t : ℝ) (H : ℕ) :
    0 ≤ sampledMoment S α t H := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The true sampled moment is bounded by geometric majorants indexed by
integer differences of squares. -/
theorem sampledMoment_le_pair_kernel (S : Finset ℤ) (α t : ℝ) (H : ℕ) :
    sampledMoment S α t H ≤
      ∑ p ∈ S ×ˢ S, linearSumBound H (α*(squareDifference p : ℝ)) := by
  calc
    sampledMoment S α t H = ‖(sampledMoment S α t H : ℂ)‖ := by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sampledMoment_nonneg _ _ _ _)]
    _ = ‖∑ p ∈ S ×ˢ S, e (t*((p.1 : ℝ)-p.2))*
        ∑ h ∈ Finset.range H, e (α*(squareDifference p : ℝ)*((h : ℝ)+1))‖ := by
      rw [sampledMoment_pair_identity]
    _ ≤ ∑ p ∈ S ×ˢ S, ‖e (t*((p.1 : ℝ)-p.2))*
        ∑ h ∈ Finset.range H, e (α*(squareDifference p : ℝ)*((h : ℝ)+1))‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [norm_mul, norm_e, one_mul]
      simpa only [e, Int.cast_one] using
        norm_exp_linear_sum_le 1 H (α*(squareDifference p : ℝ))

/-- The difference-of-squares support has radius `M^2`, rather than `2M^2`. -/
theorem squareDifference_bound (S : Finset ℤ) (M : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ))
    {p : ℤ × ℤ} (hp : p ∈ S ×ˢ S) :
    |squareDifference p| ≤ (M : ℤ)^2 := by
  rcases Finset.mem_product.mp hp with ⟨hz, hw⟩
  rcases Finset.mem_Icc.mp (hS hz) with ⟨hzlo, hzhi⟩
  rcases Finset.mem_Icc.mp (hS hw) with ⟨hwlo, hwhi⟩
  have hzsq : p.1^2 ≤ (M : ℤ)^2 := by nlinarith
  have hwsq : p.2^2 ≤ (M : ℤ)^2 := by nlinarith
  unfold squareDifference
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]

/-- Grouping by the exact difference preserves all multiplicities. -/
theorem pair_kernel_eq_fiber_sum (S : Finset ℤ) (α : ℝ) (H M : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) :
    (∑ p ∈ S ×ˢ S, linearSumBound H (α*(squareDifference p : ℝ))) =
      ∑ n ∈ Finset.Icc (-((M^2 : ℕ) : ℤ)) ((M^2 : ℕ) : ℤ),
        (differenceFiber S n).card * linearSumBound H (α*(n : ℝ)) := by
  have hmap : ∀ p ∈ S ×ˢ S,
      squareDifference p ∈ Finset.Icc (-((M^2 : ℕ) : ℤ)) ((M^2 : ℕ) : ℤ) := by
    intro p hp
    have h := abs_le.mp (squareDifference_bound S M hS hp)
    exact Finset.mem_Icc.mpr (by simpa only [Nat.cast_pow] using h)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro n _hn
  have heq : (∑ p ∈ differenceFiber S n, linearSumBound H (α*(squareDifference p : ℝ))) =
      ∑ _p ∈ differenceFiber S n, linearSumBound H (α*(n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  change (∑ p ∈ differenceFiber S n, linearSumBound H (α*(squareDifference p : ℝ))) = _
  rw [heq]
  simp

/-- The diagonal and a uniform nonzero-fiber count give the desired
reciprocal sum without an extra factor equal to the interval length. -/
theorem sampledMoment_bound_of_fiber_counts (S : Finset ℤ) (α t D : ℝ) (H M : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hzero : ((differenceFiber S 0).card : ℝ) ≤ 2*S.card)
    (hfiber : ∀ n : ℤ, n ≠ 0 → |n| ≤ (M : ℤ)^2 →
      ((differenceFiber S n).card : ℝ) ≤ 2*D) :
    sampledMoment S α t H ≤ 2*(S.card : ℝ)*H+
      4*D*∑ n ∈ Finset.range (M^2+1), linearSumBound H (α*(n : ℝ)) := by
  let I := Finset.Icc (-((M^2 : ℕ) : ℤ)) ((M^2 : ℕ) : ℤ)
  let f : ℤ → ℝ := fun n => linearSumBound H (α*(n : ℝ))
  have hpoint (n : ℤ) (hn : n ∈ I) :
      ((differenceFiber S n).card : ℝ)*f n ≤
        (if n=0 then 2*(S.card : ℝ)*H else 0)+2*D*f n := by
    by_cases hn0 : n=0
    · subst n
      have hf0 : f 0 = H := by simp [f, linearSumBound, integerDistance]
      rw [if_pos rfl, hf0]
      have hm := mul_le_mul_of_nonneg_right hzero (show (0 : ℝ) ≤ H by positivity)
      nlinarith [mul_nonneg hD (show (0 : ℝ) ≤ H by positivity)]
    · rw [if_neg hn0, zero_add]
      apply mul_le_mul_of_nonneg_right (hfiber n hn0 _) (linearSumBound_nonneg _ _)
      have hh := Finset.mem_Icc.mp hn
      exact abs_le.mpr (by simpa only [Nat.cast_pow] using hh)
  have hsym := QuadraticHeight.symmetric_sum_le_twice (M^2) f
    (fun n => linearSumBound_nonneg _ _)
    (fun n => by simp only [f, Int.cast_neg, mul_neg, QuadraticHeight.linearSumBound_neg])
  have hzero_mem : (0 : ℤ) ∈ I := by simp [I]
  calc
    sampledMoment S α t H ≤ ∑ n ∈ I, ((differenceFiber S n).card : ℝ)*f n := by
      rw [← pair_kernel_eq_fiber_sum S α H M hS]
      exact sampledMoment_le_pair_kernel S α t H
    _ ≤ ∑ n ∈ I, ((if n=0 then 2*(S.card : ℝ)*H else 0)+2*D*f n) :=
      Finset.sum_le_sum hpoint
    _ = 2*(S.card : ℝ)*H+2*D*∑ n ∈ I, f n := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [hzero_mem]
    _ ≤ 2*(S.card : ℝ)*H+2*D*(2*∑ n ∈ Finset.range (M^2+1), f (n : ℤ)) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hsym (by positivity)) _
    _ = _ := by simp only [f, Int.cast_natCast]; ring

/-- The divisor-fiber theorem supplies the nonzero multiplicities; the
zero-difference fiber contributes at most twice the size of the set. -/
theorem sampledMoment_reciprocal_bound (S : Finset ℤ) (α t D : ℝ) (H M : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → n ≤ M^2 → (n.divisors.card : ℝ) ≤ D) :
    sampledMoment S α t H ≤ 2*(S.card : ℝ)*H+
      4*D*∑ n ∈ Finset.range (M^2+1), linearSumBound H (α*(n : ℝ)) := by
  apply sampledMoment_bound_of_fiber_counts S α t D H M hS hD
  · have h := DifferenceSquaresFibers.squareDifferenceFiber_zero_card_le S S
    change (differenceFiber S 0).card ≤ 2*S.card at h
    exact_mod_cast h
  · intro n hn hnM
    have h := DifferenceSquaresFibers.squareDifferenceFiber_card_le S S hn
    change (differenceFiber S n).card ≤ 2*n.natAbs.divisors.card at h
    have hnabs : n.natAbs ≤ M^2 := by
      have hh : (n.natAbs : ℤ) ≤ (M^2 : ℕ) := by
        simpa only [Int.natCast_natAbs, Nat.cast_pow] using hnM
      exact_mod_cast hh
    have hd := hdiv n.natAbs (Int.natAbs_pos.mpr hn) hnabs
    have hR : ((differenceFiber S n).card : ℝ) ≤ 2*(n.natAbs.divisors.card : ℝ) := by
      exact_mod_cast h
    linarith

/-- A fully derived intrinsic-height estimate at the exact integer support
conductor `(M^2+1)*H`. The only divisor-size input is displayed explicitly. -/
theorem sampledMoment_intrinsic (S : Finset ℤ) (α t D : ℝ) (H M T : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → n ≤ M^2 → (n.divisors.card : ℝ) ≤ D)
    (hH : 0 < H) (hHT : (H : ℝ) ≤ 2^T) :
    let N : ℝ := (M^2+1 : ℕ)
    let L := RationalHeight.height (N*H) α
    sampledMoment S α t H ≤ 2*(S.card : ℝ)*H+
      512*D*(N*H/L+N+H+L)*(T+1 : ℕ) := by
  have hrec := ReciprocalSums.linearSumBound_sum_intrinsic α (M^2+1) H T
    (by omega) hH hHT
  have hm := mul_le_mul_of_nonneg_left hrec (show 0 ≤ 4*D by positivity)
  have hb := sampledMoment_reciprocal_bound S α t D H M hS hD hdiv
  apply hb.trans
  have hh := add_le_add_left hm (2*(S.card : ℝ)*H)
  convert hh using 1
  ring

theorem centered_card_bound (S : Finset ℤ) (M : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (hMP : (M : ℝ) ≤ P) (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) :
    (S.card : ℝ) ≤ 3*P := by
  have hcard := Finset.card_le_card hS
  have hI : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2*M+1 := by
    rw [Int.card_Icc]
    omega
  rw [hI] at hcard
  have hh : (S.card : ℝ) ≤ 2*(M : ℝ)+1 := by exact_mod_cast hcard
  linarith

/-- The ambient-length estimate keeps the desired conductor `H*P^2`, even
when the integer support radius is smaller or nonintegral. -/
theorem sampledMoment_intrinsic_ambient (S : Finset ℤ) (α t D P : ℝ) (H M T : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → n ≤ M^2 → (n.divisors.card : ℝ) ≤ D)
    (hP : 1 ≤ P) (hMP : (M : ℝ) ≤ P) (hH : 0 < H) (hHT : (H : ℝ) ≤ 2^T) :
    let L := RationalHeight.height ((H : ℝ)*P^2) α
    sampledMoment S α t H ≤ 6*P*H+
      1024*D*((H : ℝ)*P^2/L+H+P^2+L)*(T+1 : ℕ) := by
  let N : ℝ := (M^2+1 : ℕ)
  let V : ℝ := (H : ℝ)*P^2
  let L := RationalHeight.height V α
  let L₁ := RationalHeight.height (N*H) α
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hNP : N ≤ 2*P^2 := by dsimp [N]; push_cast; nlinarith
  have hV : 0 < V := mul_pos hHpos (sq_pos_of_pos hPpos)
  have hL : 0 < L := RationalHeight.height_pos _ _
  have hL₂ : 0 < RationalHeight.height (2*V) α := RationalHeight.height_pos _ _
  have hNV : N*(H : ℝ) ≤ 2*V := by dsimp [V]; nlinarith
  have hratio : N*H/L₁ ≤ 2*(V/L) := by
    have hmono := RationalHeight.conductor_div_height_mono (α := α) (mul_pos hN hHpos) hNV
    have hheight : L ≤ RationalHeight.height (2*V) α :=
      RationalHeight.height_mono_conductor (by positivity) (by linarith)
    have hdiv := div_le_div_of_nonneg_left (show 0 ≤ 2*V by positivity) hL hheight
    change N*H/L₁ ≤ 2*V/RationalHeight.height (2*V) α at hmono
    exact hmono.trans (by simpa only [mul_div_assoc] using hdiv)
  have hLcompare : L₁ ≤ 2*L := by
    have hmono := RationalHeight.height_mono_conductor (α := α) (by positivity : 0 < 2*V) hNV
    have hscale := RationalHeight.height_conductor_scale_upper (α := α) hV
      (show V ≤ 2*V by linarith)
    have hdiv : (2*V)/V = 2 := by field_simp
    rw [hdiv] at hscale
    exact hmono.trans hscale
  have hcard := centered_card_bound S M hP hMP hS
  have hdiag : 2*(S.card : ℝ)*H ≤ 6*P*H := by
    have hh := mul_le_mul_of_nonneg_right hcard hHpos.le
    nlinarith
  have hterm : N*H/L₁+N+H+L₁ ≤ 2*(V/L+H+P^2+L) := by
    nlinarith
  have hb := sampledMoment_intrinsic S α t D H M T hS hD hdiv hH hHT
  change sampledMoment S α t H ≤ 2*(S.card : ℝ)*H+
    512*D*(N*H/L₁+N+H+L₁)*(T+1 : ℕ) at hb
  apply hb.trans
  change _ ≤ 6*P*H+1024*D*(V/L+H+P^2+L)*(T+1 : ℕ)
  have hm := mul_le_mul_of_nonneg_left hterm (show 0 ≤ 512*D by positivity)
  have hmT := mul_le_mul_of_nonneg_right hm (show (0 : ℝ) ≤ (T+1 : ℕ) by positivity)
  nlinarith

/-- The ambient estimate with the logarithmic factor made explicit. -/
theorem sampledMoment_intrinsic_ambient_log (S : Finset ℤ) (α t D P : ℝ) (H M : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → n ≤ M^2 → (n.divisors.card : ℝ) ≤ D)
    (hP : 1 ≤ P) (hMP : (M : ℝ) ≤ P) (hH : 0 < H) :
    let L := RationalHeight.height ((H : ℝ)*P^2) α
    sampledMoment S α t H ≤ 6*P*H+
      1024*D*((H : ℝ)*P^2/L+H+P^2+L)*(2+Real.log (H : ℝ)/Real.log 2) := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  obtain ⟨T, hcover, hcover2⟩ := ShortHeightDistribution.exists_dyadic_cover
    (a := 1) (P := (H : ℝ)) zero_lt_one hH1
  have hHT : (H : ℝ) ≤ 2^T := by simpa only [one_mul] using hcover
  have hdepth := ShortHeightDistribution.dyadic_depth_le_log T (by norm_num : (1 : ℝ) ≤ 1)
    hHpos hcover2
  have hL := RationalHeight.height_pos ((H : ℝ)*P^2) α
  apply (sampledMoment_intrinsic_ambient S α t D P H M T hS hD hdiv hP hMP hH hHT).trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left hdepth
  positivity

/-- In the minor-height range `H≥P` and `L≥P/C`, every reciprocal term
is at most a constant times `P*H`. -/
theorem sampledMoment_minor_height_log (S : Finset ℤ) (α t D P C : ℝ) (H M : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → n ≤ M^2 → (n.divisors.card : ℝ) ≤ D)
    (hP : 1 ≤ P) (hMP : (M : ℝ) ≤ P) (hPH : P ≤ (H : ℝ))
    (_hC : 1 ≤ C) (hPL : P ≤ C*RationalHeight.height ((H : ℝ)*P^2) α) :
    sampledMoment S α t H ≤
      (6+1024*D*(C+3)*(2+Real.log (H : ℝ)/Real.log 2))*P*H := by
  let L := RationalHeight.height ((H : ℝ)*P^2) α
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hH1 : (1 : ℝ) ≤ H := hP.trans hPH
  have hHpos : (0 : ℝ) < H := zero_lt_one.trans_le hH1
  have hH : 0 < H := by exact_mod_cast hHpos
  have hL : 0 < L := RationalHeight.height_pos _ _
  have hV : 1 ≤ (H : ℝ)*P^2 := by nlinarith
  have hLsq : L^2 ≤ (H : ℝ)*P^2 := by
    have hb := RationalHeight.height_le_sqrt hV α
    have hs := pow_le_pow_left₀ hL.le hb 2
    rw [Real.sq_sqrt (by positivity)] at hs
    exact hs
  have hLPH : L ≤ P*H := by
    have hHH : (H : ℝ) ≤ (H : ℝ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hHH (sq_nonneg P)
    have hPH0 : 0 ≤ P*(H : ℝ) := by positivity
    nlinarith
  have hratio : (H : ℝ)*P^2/L ≤ C*P*H := by
    apply (div_le_iff₀ hL).mpr
    have hm := mul_le_mul_of_nonneg_left hPL (show 0 ≤ P*(H : ℝ) by positivity)
    dsimp [L] at *
    nlinarith
  have hHsmall : (H : ℝ) ≤ P*H := by nlinarith
  have hPsmall : P^2 ≤ P*H := by nlinarith
  have hterm : (H : ℝ)*P^2/L+H+P^2+L ≤ (C+3)*P*H := by nlinarith
  have hlog : 0 ≤ 2+Real.log (H : ℝ)/Real.log 2 := by
    have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hH1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hb := sampledMoment_intrinsic_ambient_log S α t D P H M hS hD hdiv hP hMP hH
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hterm (show 0 ≤ 1024*D by positivity)
  have hml := mul_le_mul_of_nonneg_right hm hlog
  change 6*P*H+1024*D*((H : ℝ)*P^2/L+H+P^2+L)*
      (2+Real.log (H : ℝ)/Real.log 2) ≤ _
  nlinarith

/-- The main `z2` resource in its exact minor range. The linear modulation
is common to all samples, and the entire centered summation set is retained. -/
theorem sampledMoment_z2_log (S : Finset ℤ) (α t D P : ℝ) (H M : ℕ)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → n ≤ M^2 → (n.divisors.card : ℝ) ≤ D)
    (hP : 1 ≤ P) (hMP : (M : ℝ) ≤ P) (hPH : P ≤ (H : ℝ))
    (hPL : P ≤ RationalHeight.height ((H : ℝ)*P^2) α) :
    sampledMoment S α t H ≤
      (6+4096*D*(2+Real.log (H : ℝ)/Real.log 2))*P*H := by
  have h := sampledMoment_minor_height_log S α t D P 1 H M hS hD hdiv hP hMP hPH
    (by norm_num) (by simpa using hPL)
  convert h using 1
  ring

/-- Fixed positive integer multipliers affect only the harmless constant. -/
theorem sampledMoment_z2_integer_coefficient_log (S : Finset ℤ)
    (α t D P : ℝ) (c H M : ℕ) (hc : 0 < c)
    (hS : S ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ)) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → n ≤ M^2 → (n.divisors.card : ℝ) ≤ D)
    (hP : 1 ≤ P) (hMP : (M : ℝ) ≤ P) (hPH : P ≤ (H : ℝ))
    (hPL : P ≤ RationalHeight.height ((H : ℝ)*P^2) α) :
    sampledMoment S ((c : ℝ)*α) t H ≤
      (6+1024*D*((c : ℝ)+3)*(2+Real.log (H : ℝ)/Real.log 2))*P*H := by
  apply sampledMoment_minor_height_log S ((c : ℝ)*α) t D P (c : ℝ) H M
    hS hD hdiv hP hMP hPH
  · exact_mod_cast hc
  · apply hPL.trans
    apply RationalHeight.height_mul_phase_lower
    · have hPpos : 0 < P := zero_lt_one.trans_le hP
      have hHpos : (0 : ℝ) < H := hPpos.trans_le hPH
      positivity
    · exact hc

/-- A real centered support condition gives the exact integer interval
needed by the difference-of-squares argument. -/
theorem centered_subset_floor (S : Finset ℤ) (P : ℝ)
    (hS : ∀ z ∈ S, |(z : ℝ)| ≤ P) :
    S ⊆ Finset.Icc (-(⌊P⌋₊ : ℤ)) (⌊P⌋₊ : ℤ) := by
  intro z hz
  have hzP := hS z hz
  have heq : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← heq] at hzP
  have hn := Nat.le_floor hzP
  have hnZ : (z.natAbs : ℤ) ≤ (⌊P⌋₊ : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hnZ
  exact Finset.mem_Icc.mpr (abs_le.mp hnZ)

/-- Centered formulation with no auxiliary integer support radius. This is
the form used for completed quadratic sums in the Waring application. -/
theorem sampledMoment_z2_centered_integer_coefficient_log (S : Finset ℤ)
    (α t D P : ℝ) (c H : ℕ) (hc : 0 < c)
    (hS : ∀ z ∈ S, |(z : ℝ)| ≤ P) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ P^2 → (n.divisors.card : ℝ) ≤ D)
    (hP : 1 ≤ P) (hPH : P ≤ (H : ℝ))
    (hPL : P ≤ RationalHeight.height ((H : ℝ)*P^2) α) :
    sampledMoment S ((c : ℝ)*α) t H ≤
      (6+1024*D*((c : ℝ)+3)*(2+Real.log (H : ℝ)/Real.log 2))*P*H := by
  have hfloor : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (zero_le_one.trans hP)
  apply sampledMoment_z2_integer_coefficient_log S α t D P c H ⌊P⌋₊ hc
    (centered_subset_floor S P hS) hD _ hP hfloor hPH hPL
  intro n hn hnM
  apply hdiv n hn
  have hcast : (n : ℝ) ≤ (⌊P⌋₊ : ℝ)^2 := by exact_mod_cast hnM
  nlinarith [show (0 : ℝ) ≤ (⌊P⌋₊ : ℝ) by positivity]

#print axioms sampledMoment_pair_identity
#print axioms sampledMoment_reciprocal_bound
#print axioms sampledMoment_intrinsic_ambient_log
#print axioms sampledMoment_z2_log
#print axioms sampledMoment_z2_integer_coefficient_log
#print axioms sampledMoment_z2_centered_integer_coefficient_log

end Waring.SampledQuadraticSecond
