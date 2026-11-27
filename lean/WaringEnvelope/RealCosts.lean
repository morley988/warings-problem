import WaringEnvelope.LogBounds

/-! # Real interpretation of the outward-rounded interval charges -/
noncomputable section
namespace WaringEnvelope

theorem le_ceilDiv_mul (a b : ℕ) (hb : 0<b) : a ≤ ceilDiv a b*b := by
  have hsum := Nat.mod_add_div (a+b-1) b
  have hm := Nat.mod_lt (a+b-1) hb
  unfold ceilDiv
  rw [Nat.mul_comm b _] at hsum
  omega

theorem real_le_ceilDiv (a b : ℕ) (hb : 0<b) : (a:ℝ)/b ≤ (ceilDiv a b : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hb : (0:ℝ)<b)).mpr
  exact_mod_cast le_ceilDiv_mul a b hb

/-- Each exact integer charge dominates the integral of 2/(t L) over the
corresponding height interval, with L the retained conductor. -/
theorem intervalCost_sound (z z' m : ℕ) (hz : 0<z') (hzz : z'≤z) (hm : 0<m) :
    2*Real.log ((z:ℝ)/z')/((U:ℝ)*m/(V*B)) ≤ (intervalCost z z' m:ℝ)/D := by
  have hzp : (0:ℝ)<z' := by exact_mod_cast hz
  have hzp' : (0:ℝ)<z := by exact_mod_cast hz.trans_le hzz
  have hmp : (0:ℝ)<m := by exact_mod_cast hm
  have hU : (0:ℝ)<U := by norm_num [U]
  have hV : (0:ℝ)<V := by norm_num [V]
  have hB : (0:ℝ)<B := by norm_num [B]
  have hD : (0:ℝ)<D := by norm_num [D]
  have hden : 0 < z*z'*U*m := by
    have : 0<U := by decide
    have : 0<z := hz.trans_le hzz
    positivity
  have hsq : z'^2 ≤ z^2 := Nat.pow_le_pow_left hzz _
  have h := real_le_ceilDiv (D*(z^2-z'^2)*B*V) (z*z'*U*m) hden
  push_cast [Nat.cast_sub hsq] at h
  have hx : 1≤(z:ℝ)/z' := by rw [le_div_iff₀ hzp,one_mul]; exact_mod_cast hzz
  have hlog := twice_log_le_sub_inv _ hx
  have hL : 0 < (U:ℝ)*m/(V*B) := by positivity
  calc
    _ ≤ (((z:ℝ)/z')-((z:ℝ)/z')⁻¹)/((U:ℝ)*m/(V*B)) :=
      div_le_div_of_nonneg_right hlog hL.le
    _ = ((D:ℝ)*((z:ℝ)^2-(z':ℝ)^2)*B*V/((z:ℝ)*z'*U*m))/D := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h hD.le

#print axioms intervalCost_sound
end WaringEnvelope
