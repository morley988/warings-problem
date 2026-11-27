import WaringSiegel.WSL4ArchMixedNumerical

/-! # Real-power scale algebra attached to the mixed complementary integral -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4

private theorem monomial_cube_division (X Y a b c e : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    (X/Y^3)^a*X^b*Y^c*(X/Y)^e = X^(a+b+e)*Y^(c-3*a-e) := by
  have ht : (X/Y^3)^a = X^a*Y^(-(3*a)) := by
    rw [Real.div_rpow hX.le (pow_nonneg hY.le _)]
    have hp : (Y^3)^a = Y^((3:ℝ)*a) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY.le]
      norm_num
    rw [hp,Real.rpow_neg hY.le,div_eq_mul_inv]
  have hz : (X/Y)^e = X^e*Y^(-e) := by
    rw [Real.div_rpow hX.le hY.le,Real.rpow_neg hY.le,div_eq_mul_inv]
  rw [ht,hz]
  calc
    _ = (X^a*X^b*X^e)*(Y^c*Y^(-(3*a))*Y^(-e)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hX,← Real.rpow_add hX,← Real.rpow_add hY,← Real.rpow_add hY]
      congr 2

private theorem mixed_scale_term (X Y δ a b c : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    (X/Y^3)*X^(1+δ)*(X/Y)^(2+δ)*(Y^a*(X/Y^3)^b*(X/Y)^c) =
      X^(4+2*δ+b+c)*Y^(a-5-δ-3*b-c) := by
  have ht : 0 < X/Y^3 := div_pos hX (pow_pos hY _)
  have hz : 0 < X/Y := div_pos hX hY
  calc
    _ = (X/Y^3)^(1+b)*X^(1+δ)*Y^a*(X/Y)^(2+δ+c) := by
      rw [Real.rpow_add ht 1 b,Real.rpow_one,Real.rpow_add hz (2+δ) c]
      ring
    _ = X^((1+b)+(1+δ)+(2+δ+c))*Y^(a-3*(1+b)-(2+δ+c)) :=
      monomial_cube_division X Y (1+b) (1+δ) a (2+δ+c) hX hY
    _ = _ := by congr 1 <;> congr 1 <;> ring

/-- The complete complementary polynomial has the manuscript's three
squared monomials, with a controlled epsilon loss. -/
theorem mixed_complement_scale_polynomial (X Y δ : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hδ : 0 ≤ δ) :
    (X/Y^3)*X^(1+δ)*(X/Y)^(2+δ)*
      ((X/Y^3)*Y*(X/Y)^(2+δ)+Y^2*(X/Y^3)^((3:ℝ)/4+δ)*(X/Y)^(2+δ)+
        Y^2*(X/Y^3)^((1:ℝ)/4+δ)*(X/Y)^((9:ℝ)/4+δ)) ≤
      X^(4*δ)*((X^((7:ℝ)/2)*Y^(-(9/2):ℝ))^2+
        (X^((27:ℝ)/8)*Y^(-(29/8):ℝ))^2+
        (X^((13:ℝ)/4)*Y^(-3:ℝ))^2) := by
  have hXp : 0 < X := by linarith
  have hYp : 0 < Y := by linarith
  have h0 := mixed_scale_term X Y δ 1 1 (2+δ) hXp hYp
  have h1 := mixed_scale_term X Y δ 2 ((3:ℝ)/4+δ) (2+δ) hXp hYp
  have h2 := mixed_scale_term X Y δ 2 ((1:ℝ)/4+δ) ((9:ℝ)/4+δ) hXp hYp
  have he0 : 4+2*δ+1+(2+δ)=7+3*δ := by ring
  have he01 : 1-5-δ-3*1-(2+δ) = -9-2*δ := by ring
  have he1 : 4+2*δ+(3/4+δ)+(2+δ) = 27/4+4*δ := by ring
  have he11 : 2-5-δ-3*(3/4+δ)-(2+δ) = -(29/4)-5*δ := by ring
  have he2 : 4+2*δ+(1/4+δ)+(9/4+δ) = 13/2+4*δ := by ring
  have he21 : 2-5-δ-3*(1/4+δ)-(9/4+δ) = -6-5*δ := by ring
  rw [he0,he01] at h0
  rw [he1,he11,Real.rpow_ofNat] at h1
  rw [he2,he21,Real.rpow_ofNat] at h2
  simp only [Real.rpow_one] at h0
  have hb0 : X^(7+3*δ)*Y^(-9-2*δ) ≤ X^(7+4*δ)*Y^(-9:ℝ) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_le hX (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hY (by linarith))
      (Real.rpow_nonneg hYp.le _) (Real.rpow_nonneg hXp.le _)
  have hb1 : X^((27:ℝ)/4+4*δ)*Y^(-(29/4)-5*δ) ≤ X^((27:ℝ)/4+4*δ)*Y^(-(29/4):ℝ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by linarith))
      (Real.rpow_nonneg hXp.le _)
  have hb2 : X^((13:ℝ)/2+4*δ)*Y^(-6-5*δ) ≤ X^((13:ℝ)/2+4*δ)*Y^(-6:ℝ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by linarith))
      (Real.rpow_nonneg hXp.le _)
  have hs (a b : ℝ) : (X^a*Y^b)^2 = X^(2*a)*Y^(2*b) := by
    rw [mul_pow,← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hXp.le,
      ← Real.rpow_mul hYp.le]
    congr 1 <;> congr 1 <;> norm_num <;> ring
  calc
    _ = X^(7+3*δ)*Y^(-9-2*δ)+X^((27:ℝ)/4+4*δ)*Y^(-(29/4)-5*δ)+
        X^((13:ℝ)/2+4*δ)*Y^(-6-5*δ) := by
      rw [mul_add,mul_add]
      rw [show (X/Y^3)*Y*(X/Y)^(2+δ)=Y*(X/Y^3)*(X/Y)^(2+δ) by ring,h0,h1,h2]
    _ ≤ X^(7+4*δ)*Y^(-9:ℝ)+X^((27:ℝ)/4+4*δ)*Y^(-(29/4):ℝ)+
        X^((13:ℝ)/2+4*δ)*Y^(-6:ℝ) := add_le_add (add_le_add hb0 hb1) hb2
    _ = _ := by
      rw [hs,hs,hs]
      norm_num
      rw [Real.rpow_add hXp,Real.rpow_add hXp,Real.rpow_add hXp]
      norm_num only [Real.rpow_ofNat]
      ring

/-- Taking square roots introduces no extra scale factor. -/
theorem mixed_complement_scale_sqrt {C S X Y ε : ℝ} (hC : 0 < C) (hS : 0 ≤ S)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hε : 0 ≤ ε)
    (hb : S^2 ≤ C*((X/Y^3)*X^(1+ε/2)*(X/Y)^(2+ε/2)*
      ((X/Y^3)*Y*(X/Y)^(2+ε/2)+Y^2*(X/Y^3)^((3:ℝ)/4+ε/2)*(X/Y)^(2+ε/2)+
        Y^2*(X/Y^3)^((1:ℝ)/4+ε/2)*(X/Y)^((9:ℝ)/4+ε/2)))) :
    S ≤ Real.sqrt C*X^ε*(X^((7:ℝ)/2)*Y^(-(9/2):ℝ)+
      X^((13:ℝ)/4)*Y^(-3:ℝ)+X^((27:ℝ)/8)*Y^(-(29/8):ℝ)) := by
  have hXp : 0 < X := by linarith
  have hYp : 0 < Y := by linarith
  let a := X^((7:ℝ)/2)*Y^(-(9/2):ℝ)
  let b := X^((13:ℝ)/4)*Y^(-3:ℝ)
  let c := X^((27:ℝ)/8)*Y^(-(29/8):ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hbb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoly := mixed_complement_scale_polynomial X Y (ε/2) hX hY (by positivity)
  have hpoly' : S^2 ≤ C*X^(2*ε)*(a^2+c^2+b^2) := by
    apply hb.trans
    simpa only [show (4:ℝ)*(ε/2)=2*ε by ring,mul_assoc,a,b,c] using
      mul_le_mul_of_nonneg_left hpoly hC.le
  have hsum : a^2+c^2+b^2 ≤ (a+b+c)^2 := by
    nlinarith [mul_nonneg ha hbb,mul_nonneg ha hc,mul_nonneg hbb hc]
  have hsum' := hpoly'.trans (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg hC.le (Real.rpow_nonneg hXp.le _)))
  have hx : (X^ε)^2 = X^(2*ε) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hXp.le]
    congr 1 <;> norm_num <;> ring
  have he : (Real.sqrt C*X^ε*(a+b+c))^2 = C*X^(2*ε)*(a+b+c)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hC.le,hx]
  have hn : 0 ≤ Real.sqrt C*X^ε*(a+b+c) := by positivity
  change S ≤ Real.sqrt C*X^ε*(a+b+c)
  rw [← he] at hsum'
  nlinarith

#print axioms mixed_complement_scale_polynomial
#print axioms mixed_complement_scale_sqrt
end WaringSiegel.WSL4
