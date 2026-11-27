import WaringSiegel.WSL4ArchProductRegion

/-! # Scalar kernel bounds for the auxiliary broad-major pruning -/
noncomputable section
set_option maxHeartbeats 1000000
namespace WaringSiegel.WSL4

theorem one_add_eighth_le (u : ℝ) (hu : 0≤u) :
    (1+u)^8≤(2:ℝ)^8*(1+u^8) := by
  by_cases h : u≤1
  · have hp := pow_le_pow_left₀ (by linarith : 0≤1+u) (by linarith : 1+u≤2) 8
    exact hp.trans (le_mul_of_one_le_right (by positivity)
      (by nlinarith [pow_nonneg hu 8]))
  · have hu1 : 1≤u := le_of_lt (lt_of_not_ge h)
    have hp := pow_le_pow_left₀ (by positivity : 0≤1+u) (by linarith : 1+u≤2*u) 8
    rw [mul_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left (by linarith : u^8≤1+u^8) (by positivity))

theorem cubic_pruning_scalar_bound (q A X Y L C0 : ℝ)
    (hq : 0<q) (hA : 0<A) (hX : 0<X) (hY : 0≤Y) (hL : 0<L) (hC : 1≤C0)
    (hLA : L≤q*A) (hAX : q*A≤C0*X) :
    A^(-(4:ℝ))*(1+Y*q*A/X)^8 ≤
      (2:ℝ)^8*C0^((27:ℝ)/4)*q^((5:ℝ)/4)*A^(-(11:ℝ)/4)*
        (1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) := by
  let r : ℝ := (5:ℝ)/4
  let b : ℝ := (27:ℝ)/4
  let W : ℝ := q^r*A^(-(11:ℝ)/4)
  let z : ℝ := q*A/X
  have hz : 0<z := div_pos (mul_pos hq hA) hX
  have hzC : z≤C0 := (div_le_iff₀ hX).mpr hAX
  have hC0 : 0<C0 := lt_of_lt_of_le zero_lt_one hC
  have hCb : 1≤C0^b := Real.one_le_rpow hC (by dsimp [b]; norm_num)
  have hW : 0≤W := by dsimp [W]; positivity
  have hfactor : A^(-(4:ℝ))*(q*A)^r=W := by
    rw [Real.mul_rpow hq.le hA.le]
    calc
      _ = q^r*(A^(-(4:ℝ))*A^r) := by ring
      _ = W := by rw [← Real.rpow_add hA]; dsimp [W,r]; norm_num
  have hbase : A^(-(4:ℝ))≤W/L^r := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL r)).mpr
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hL.le hLA (by dsimp [r]; norm_num)) (Real.rpow_nonneg hA.le _)
  have hp : z^8≤C0^b*z^r := by
    have he : (8:ℝ)=b+r := by dsimp [b,r]; norm_num
    rw [← Real.rpow_natCast z 8]
    change z^(8:ℝ)≤C0^b*z^r
    rw [he,Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hz.le hzC (by dsimp [b]; norm_num)) (Real.rpow_nonneg hz.le _)
  have hzfactor : A^(-(4:ℝ))*z^r=W/X^r := by
    dsimp only [z]
    rw [Real.div_rpow (mul_pos hq hA).le hX.le,← mul_div_assoc,hfactor]
  have hpower : A^(-(4:ℝ))*(Y*z)^8≤C0^b*W*Y^8/X^r := by
    rw [mul_pow]
    calc
      _ = Y^8*(A^(-(4:ℝ))*z^8) := by ring
      _ ≤ Y^8*(A^(-(4:ℝ))*(C0^b*z^r)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hA.le _)) (by positivity)
      _ = C0^b*Y^8*(A^(-(4:ℝ))*z^r) := by ring
      _ = _ := by rw [hzfactor]; ring
  have hu : 0≤Y*z := mul_nonneg hY hz.le
  have he : Y*q*A/X=Y*z := by dsimp [z]; ring
  rw [he]
  calc
    _ ≤ A^(-(4:ℝ))*((2:ℝ)^8*(1+(Y*z)^8)) :=
      mul_le_mul_of_nonneg_left (one_add_eighth_le _ hu) (Real.rpow_nonneg hA.le _)
    _ = (2:ℝ)^8*(A^(-(4:ℝ))+A^(-(4:ℝ))*(Y*z)^8) := by ring
    _ ≤ (2:ℝ)^8*(C0^b*W/L^r+C0^b*W*Y^8/X^r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ hpower
      exact hbase.trans (by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
        exact le_mul_of_one_le_left hW hCb)
    _ = _ := by dsimp [W,b,r]; ring

#print axioms cubic_pruning_scalar_bound
end WaringSiegel.WSL4
