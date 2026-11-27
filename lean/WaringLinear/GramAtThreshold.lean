import WaringLinear.GramSpectrum
import WaringLinear.SpectralCutoff

/-! # Fibre square bound with the logarithm and conductor saving explicit -/
noncomputable section
open scoped BigOperators Classical
namespace WaringLinear
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- An `X^(1-σ)` off-block entry and a `CX` small-block operator give the
truncated square mass at `X^(1-z)/2`, with `32E ≤ X^(σ-2z)`.
The result applies to the actual inner products of the Fourier rows. -/
theorem gram_fibre_at_amplitude (v : ι→V) (c : V) (X C E z σ : ℝ)
    (hX : 1≤X) (hC : 0≤C) (hE : 0≤E) (hz : 0≤z)
    (hcoeff : ‖c‖^2≤X) (hslack : 32*E≤X^(σ-2*z))
    (hupper : ∀i,‖inner ℂ (v i) c‖≤X)
    (hGram : ∀ (t : Finset ι) (w : t → ℂ),
      ‖∑ i,w i • v i.1‖^2 ≤ (C*X)*(∑ i,‖w i‖^2)+(E*X^(1-σ))*(∑ i,‖w i‖)^2) :
    (∑i,{u:ℝ | X^(1-z)/2≤u}.indicator (fun u => u^2) ‖inner ℂ (v i) c‖) ≤
      ((18+8*z*Real.logb 2 X)*C)*X^2 := by
  classical
  have hx := lt_of_lt_of_le zero_lt_one hX
  let Y := X^(1-z)/2
  have hy : 0<Y := by dsimp [Y]; positivity
  have hyx : Y≤X := by
    have h := Real.rpow_le_rpow_of_exponent_le hX (show 1-z≤1 by linarith)
    rw [Real.rpow_one] at h
    dsimp [Y]
    linarith
  obtain ⟨J,hj,hdlo,hdhi⟩ := spectral_cutoff_exists X Y hy hyx
  have hlog : Real.logb 2 (X/Y)=1+z*Real.logb 2 X := by
    rw [Real.logb_div hx.ne' hy.ne']
    dsimp [Y]
    rw [Real.logb_div (Real.rpow_pos_of_pos hx _).ne' (by norm_num),
      Real.logb_self_eq_one (by norm_num),Real.logb_rpow_eq_mul_logb_of_pos hx]
    ring
  rw [hlog] at hj
  have hrp : X*X^(1-σ)*X^(σ-2*z)=(X^(1-z))^2 := by
    rw [←Real.rpow_two,←Real.rpow_mul hx.le]
    calc
      X*X^(1-σ)*X^(σ-2*z)=X^(1:ℝ)*X^(1-σ)*X^(σ-2*z) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hx,←Real.rpow_add hx]; congr 1; ring
  have hsl := mul_le_mul_of_nonneg_left hslack (mul_nonneg hx.le (Real.rpow_nonneg hx.le (1-σ)))
  have hc := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hE (Real.rpow_nonneg hx.le (1-σ)))
  have hab : 2*‖c‖^2*(E*X^(1-σ))≤(Y/2)^2 := by
    dsimp [Y]
    nlinarith only [hsl,hc,hrp]
  have hh := gram_truncated_fibre v c X (C*X) (E*X^(1-σ)) hx
    (mul_nonneg hC hx.le) (mul_nonneg hE (Real.rpow_nonneg hx.le _)) J hupper hGram
    (hab.trans (pow_le_pow_left₀ (by positivity) hdlo.le 2))
  have hi := indicator_sum_le_spectrum (fun i => ‖inner ℂ (v i) c‖) X Y hx J hdhi
  apply (hi.trans hh).trans
  calc
    _ ≤ (1+4*(J:ℝ))*(2*(C*X)*X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ ≤ ((18+8*z*Real.logb 2 X)*C)*X^2 := by
      have hc0 := mul_le_mul_of_nonneg_right
        (show (1+4*(J:ℝ))*2 ≤ 18+8*z*Real.logb 2 X by linarith only [hj])
        (mul_nonneg hC (sq_nonneg X))
      linarith only [hc0]

#print axioms gram_fibre_at_amplitude
end WaringLinear
