import WaringLinear.ArcApproximation

/-! # Uniform major-arc approximation for the marked support -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators Interval
namespace WaringLinear

/-- Dilation recovers the same archimedean integral for each choice of marks.
The final incomplete interval costs at most one. -/
theorem marked_cofactor_integral (c d P : ℝ) (k N : ℕ) (hd : 0<d)
    (hlo : d*N≤P) (hhi : P≤d*(N+1)) :
    ‖(∫ x in (0:ℝ)..N, monomialWeight (c*d^k) k x) -
      (d⁻¹:ℝ) • ∫ x in (0:ℝ)..P, monomialWeight c k x‖ ≤ 1 := by
  let w := monomialWeight c k
  have hc : Continuous w := continuous_monomialWeight c k
  have hid (x : ℝ) : monomialWeight (c*d^k) k x = w (d*x) := by
    simp [w,monomialWeight,mul_pow,mul_assoc]
  simp only [hid,intervalIntegral.integral_comp_mul_left w hd.ne',mul_zero,←smul_sub]
  have htail : (∫ x in (0:ℝ)..d*N, w x) - ∫ x in (0:ℝ)..P, w x =
      -(∫ x in d*N..P, w x) := by
    rw [←intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 (d*N)) (hc.intervalIntegrable (d*N) P)]
    abel
  rw [htail,norm_smul,norm_neg,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
  have hnorm : ‖∫ x in d*N..P, w x‖ ≤ 1*|P-d*N| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    exact (Complex.norm_exp_ofReal_mul_I _).le
  rw [abs_of_nonneg (sub_nonneg.mpr hlo),one_mul] at hnorm
  have := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith : P-d*N≤d)) (inv_pos.mpr hd).le
  simpa [hd.ne'] using this

/-- Each cofactor has the same complete mean, as supplied for a unit
dilation by `complete_unit_dilation`. The error is proportional to the
number of marked products, uniformly through the common polynomial arc. -/
theorem marked_support_arc_approximation {ι : Type*} (D : Finset ι)
    (z : ι → ℕ → ℂ) (d : ι → ℝ) (N : ι → ℕ) (q k : ℕ) (hq : 0<q)
    (a : ℂ) (c P : ℝ) (ha : ‖a‖≤1)
    (hd : ∀ i∈D, 0<d i) (hlo : ∀ i∈D, d i*N i≤P)
    (hhi : ∀ i∈D, P≤d i*(N i+1)) (hz : ∀ i∈D, ∀ n, ‖z i n‖≤1)
    (hper : ∀ i∈D, ∀ n, z i (n+q)=z i n)
    (hmean : ∀ i∈D, ∑ n ∈ range q, z i n=(q:ℂ)*a) :
    ‖(∑ i∈D, ∑ n∈range (N i), monomialWeight (c*(d i)^k) k n*z i n) -
      a*((∑ i∈D,(d i)⁻¹) • ∫ x in (0:ℝ)..P, monomialWeight c k x)‖ ≤
      (D.card:ℝ)*(2*(q:ℝ)*(1+2*|c| *P^k)+2*|c| *P^k+1) := by
  let I := ∫ x in (0:ℝ)..P, monomialWeight c k x
  let T := fun i => ∑ n∈range (N i), monomialWeight (c*(d i)^k) k n*z i n
  let J := fun i => ∫ x in (0:ℝ)..N i, monomialWeight (c*(d i)^k) k x
  let E := 2*(q:ℝ)*(1+2*|c| *P^k)+2*|c| *P^k+1
  change ‖(∑ i∈D,T i) - a*((∑ i∈D,(d i)⁻¹) • I)‖ ≤ (D.card:ℝ)*E
  rw [Finset.sum_smul,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i∈D,E := by
      apply Finset.sum_le_sum
      intro i hi
      have di := hd i hi
      have h1 := polynomial_major_arc_approximation (z i) q (N i) k hq a (c*(d i)^k)
        ha (hz i hi) (hper i hi) (hmean i hi)
      change ‖T i-a*J i‖≤_ at h1
      have h2 := marked_cofactor_integral c (d i) P k (N i) di (hlo i hi) (hhi i hi)
      change ‖J i - (d i)⁻¹ • I‖ ≤ 1 at h2
      have hscale : 2*|c*(d i)^k| *((N i:ℕ):ℝ)^k ≤ 2*|c| *P^k := by
        rw [abs_mul,abs_of_nonneg (pow_nonneg di.le _)]
        rw [show 2*(|c| *(d i)^k)*((N i:ℕ):ℝ)^k =
          2*|c| *(d i*((N i:ℕ):ℝ))^k by rw [mul_pow]; ring]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg di.le (Nat.cast_nonneg _)) (hlo i hi) k) (by positivity)
      have h3 : ‖a*(J i-(d i)⁻¹ • I)‖ ≤ 1 := by
        rw [Complex.norm_mul]
        exact (mul_le_mul ha h2 (norm_nonneg _) zero_le_one).trans (by norm_num)
      rw [show T i-a*((d i)⁻¹ • I) =
        (T i-a*J i)+a*(J i-(d i)⁻¹ • I) by ring]
      apply (norm_add_le _ _).trans
      dsimp only [E]
      have hq' : 0≤2*(q:ℝ) := by positivity
      nlinarith only [h1,h3,hscale,mul_le_mul_of_nonneg_left hscale hq']
    _ = _ := by simp

#print axioms marked_cofactor_integral
#print axioms marked_support_arc_approximation
end WaringLinear
