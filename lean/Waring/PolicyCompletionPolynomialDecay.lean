import Waring.PolicyCompletionPolynomialCalculus

/-!
# Uniform power decay for the actual auxiliary polynomial integral

A single positive coefficient of degree d controls the singular integral.
All remaining coefficients may vary independently as long as they are
nonnegative. This is the exact phase property of the centered differences.
-/

noncomputable section
open MeasureTheory
namespace Waring.PolicyCompletionPolynomialDecay
open Polynomial QuadraticModulation EndgameCompletion
open PolicyCompletionPolynomialDiscrete PolicyCompletionPolynomialCalculus

theorem norm_polynomial_integral_tail_le_coefficient (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) {d : ℕ} {H A P β : ℝ}
    (hd : 1 ≤ d) (hH : 0 < H) (hcoeff : H ≤ f.coeff d)
    (hA : 0 < A) (hAP : A ≤ P) (hβ : β ≠ 0) :
    ‖∫ t in A..P, e (β*f.eval t)‖ ≤ 1/(Real.pi*|β| *H*(d:ℝ)*A^(d-1)) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hlower := derivative_eval_lower f hf hd hH hcoeff hA.le
  have hfirst : 0 < f.derivative.eval A := (by positivity : 0<H*(d:ℝ)*A^(d-1)).trans_le hlower
  apply (norm_polynomial_integral_tail_le f hf hA.le hAP hβ hfirst).trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  calc
    Real.pi*|β| *H*(d:ℝ)*A^(d-1) = Real.pi*|β| *(H*(d:ℝ)*A^(d-1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)

theorem norm_polynomialIntegral_split_le (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) {d : ℕ} {H A P β : ℝ}
    (hd : 1 ≤ d) (hH : 0 < H) (hcoeff : H ≤ f.coeff d)
    (hA : 0 < A) (hAP : A ≤ P) (hβ : β ≠ 0) :
    ‖polynomialIntegral f P β‖ ≤ A+1/(Real.pi*|β| *H*(d:ℝ)*A^(d-1)) := by
  unfold polynomialIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_polynomial_e f β).intervalIntegrable 0 A)
    ((continuous_polynomial_e f β).intervalIntegrable A P)]
  exact (norm_add_le _ _).trans (add_le_add (norm_polynomialIntegral_le f hA.le β)
    (norm_polynomial_integral_tail_le_coefficient f hf hd hH hcoeff hA hAP hβ))

theorem norm_polynomialIntegral_le_at_scale (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) {d : ℕ} {H A P β : ℝ}
    (hd : 1 ≤ d) (hH : 0 < H) (hcoeff : H ≤ f.coeff d)
    (hA : 0 < A) (hP : 0 ≤ P) (hscale : |β| *H*A^d=1) :
    ‖polynomialIntegral f P β‖ ≤ (1+1/(Real.pi*(d:ℝ)))*A := by
  have hcoef : 0 ≤ 1/(Real.pi*(d:ℝ)) := by positivity
  by_cases hAP : A ≤ P
  · have hβ : β ≠ 0 := by intro h; simp [h] at hscale
    have hd0 : (d:ℝ)≠0 := by exact_mod_cast (by omega : d≠0)
    have hpow : A^(d-1)*A=A^d := by rw [← pow_succ, Nat.sub_add_cancel hd]
    have htail : 1/(Real.pi*|β| *H*(d:ℝ)*A^(d-1))=A/(Real.pi*(d:ℝ)) := by
      field_simp [Real.pi_ne_zero, hd0, abs_ne_zero.mpr hβ, hH.ne', hA.ne']
      calc
        1 = |β| *H*A^d := hscale.symm
        _ = _ := by rw [← hpow]; ring
    calc
      _ ≤ A+1/(Real.pi*|β| *H*(d:ℝ)*A^(d-1)) :=
        norm_polynomialIntegral_split_le f hf hd hH hcoeff hA hAP hβ
      _ = _ := by rw [htail]; ring
  · exact (norm_polynomialIntegral_le f hP β).trans ((le_of_not_ge hAP).trans (by nlinarith))

theorem norm_polynomialIntegral_decay (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) {d : ℕ} {H P β : ℝ}
    (hd : 1 ≤ d) (hH : 0 < H) (hcoeff : H ≤ f.coeff d)
    (hP : 0 ≤ P) (hβ : β ≠ 0) :
    ‖polynomialIntegral f P β‖ ≤ 2*(|β| *H)^(-(d:ℝ)⁻¹) := by
  have hd0 : (d:ℝ)≠0 := by exact_mod_cast (by omega : d≠0)
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hγ : 0 < |β| *H := mul_pos (abs_pos.mpr hβ) hH
  have hscale : |β| *H*((|β| *H)^(-(d:ℝ)⁻¹))^d=1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hγ.le, neg_mul,
      inv_mul_cancel₀ hd0, Real.rpow_neg_one, mul_inv_cancel₀ hγ.ne']
  have hbound := norm_polynomialIntegral_le_at_scale f hf hd hH hcoeff
    (Real.rpow_pos_of_pos hγ _) hP hscale
  have hπd : 1 ≤ Real.pi*(d:ℝ) := by nlinarith [Real.two_le_pi]
  have hcoef : 1+1/(Real.pi*(d:ℝ)) ≤ 2 := by
    have := (div_le_one (lt_of_lt_of_le zero_lt_one hπd)).mpr hπd
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hγ.le _))

theorem norm_polynomialIntegral_weight (f : Polynomial ℝ)
    (hf : NonnegativeCoefficients f) {d : ℕ} {H P β : ℝ}
    (hd : 1 ≤ d) (hH : 0 < H) (hcoeff : H ≤ f.coeff d) (hP : 0 < P) :
    ‖polynomialIntegral f P β‖ ≤ 4*P*(1+|β| *H*P^d)^(-(d:ℝ)⁻¹) := by
  let θ : ℝ := (d:ℝ)⁻¹
  let u : ℝ := |β| *H*P^d
  have hdR : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hθ : 0 ≤ θ := inv_nonneg.mpr hdR.le
  have hθ1 : θ ≤ 1 := (inv_le_one₀ hdR).mpr hd1
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hbase : 0 < 1+u := by linarith
  have htwo : (2:ℝ)^θ ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hθ1
  have hnorm := norm_polynomialIntegral_le f hP.le β
  have hmul : ‖polynomialIntegral f P β‖*(1+u)^θ ≤ 4*P := by
    by_cases husmall : u ≤ 1
    · have hw : (1+u)^θ ≤ 2 :=
        (Real.rpow_le_rpow hbase.le (by linarith) hθ).trans htwo
      have hh := mul_le_mul hnorm hw (Real.rpow_nonneg hbase.le _) hP.le
      nlinarith
    · have hu1 : 1 ≤ u := (lt_of_not_ge husmall).le
      have hβ : β≠0 := by intro h; simp [u,h] at husmall
      have hγ : 0 < |β| *H := mul_pos (abs_pos.mpr hβ) hH
      have huθ : u^θ = (|β| *H)^θ*P := by
        dsimp [u]
        rw [Real.mul_rpow hγ.le (pow_nonneg hP.le _), ← Real.rpow_natCast,
          ← Real.rpow_mul hP.le]
        simp only [θ, mul_inv_cancel₀ hdR.ne', Real.rpow_one]
      have hw : (1+u)^θ ≤ 2*((|β| *H)^θ*P) := by
        calc
          _ ≤ (2*u)^θ := Real.rpow_le_rpow hbase.le (by linarith) hθ
          _ = (2:ℝ)^θ*u^θ := Real.mul_rpow (by norm_num) hu
          _ ≤ 2*u^θ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hu _)
          _ = _ := by rw [huθ]
      have hdec := norm_polynomialIntegral_decay f hf hd hH hcoeff hP.le hβ
      calc
        _ ≤ (2*(|β| *H)^(-θ))*(2*((|β| *H)^θ*P)) :=
          mul_le_mul hdec hw (Real.rpow_nonneg hbase.le _) (by positivity)
        _ = 4*P := by
          have hid : (|β| *H)^(-θ)*(|β| *H)^θ=1 := by
            rw [← Real.rpow_add hγ, neg_add_cancel, Real.rpow_zero]
          calc
            _ = 4*P*((|β| *H)^(-θ)*(|β| *H)^θ) := by ring
            _ = _ := by rw [hid,mul_one]
  have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hbase θ)).mpr hmul
  simpa only [u, θ, Real.rpow_neg hbase.le, div_eq_mul_inv] using hdiv

#print axioms norm_polynomialIntegral_decay
#print axioms norm_polynomialIntegral_weight
end Waring.PolicyCompletionPolynomialDecay
