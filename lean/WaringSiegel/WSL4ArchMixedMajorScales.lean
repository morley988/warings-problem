import WaringSiegel.WSL4ArchMixedScales

/-! # Exact scale algebra for the enlarged mixed-major integral -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped Classical
namespace WaringSiegel.WSL4

theorem mixed_major_scale_polynomial (X Y L ε : ℝ) (hX : 0<X) (hY : 0<Y) (hL : 0<L) :
    (X/Y^3)*X*X^(ε/2)*Y*((X/Y)^3)⁻¹*
      ((X/Y)^4+(L*X)^((7/2:ℝ)+ε/2)) =
    X^(3+ε/2)*Y^(-3:ℝ)+L^((7/2:ℝ)+ε/2)*X^((5/2:ℝ)+ε)*Y := by
  have hx : X^(ε/2)*X^((7/2:ℝ)+ε/2)/X = X^((5/2:ℝ)+ε) := by
    calc
      _ = X^(ε/2+((7/2:ℝ)+ε/2))/X^(1:ℝ) := by rw [Real.rpow_add hX (ε/2) ((7/2:ℝ)+ε/2),Real.rpow_one]
      _ = X^(ε/2+((7/2:ℝ)+ε/2)-1) := (Real.rpow_sub hX _ _).symm
      _ = _ := by congr 1 <;> ring
  have hy : Y^(-3:ℝ)=(Y^3)⁻¹ := by rw [Real.rpow_neg hY.le,Real.rpow_ofNat]
  rw [Real.mul_rpow hL.le hX.le]
  calc
    _ = X^3*X^(ε/2)/Y^3 + L^((7/2:ℝ)+ε/2)*(X^(ε/2)*X^((7/2:ℝ)+ε/2)/X)*Y := by
      field_simp [hX.ne',hY.ne']
      <;> ring
    _ = _ := by rw [hx,hy,Real.rpow_add hX 3 (ε/2),Real.rpow_ofNat]; ring

theorem mixed_major_monomials_domination (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (hYX : Y^7≤X) :
    X^(3:ℝ)*Y^(-3:ℝ)+X^((5/2):ℝ)*Y ≤ 2*X^((7/2):ℝ)*Y^(-(9/2):ℝ) := by
  have hXp : 0<X := by linarith
  have hYp : 0<Y := by linarith
  have hh : Y^((3/2):ℝ)≤X^((1/2):ℝ) := by
    have h0 := Real.rpow_le_rpow (pow_nonneg hYp.le 7) hYX (by norm_num : (0:ℝ)≤1/2)
    rw [← Real.rpow_natCast,← Real.rpow_mul hYp.le] at h0
    exact (Real.rpow_le_rpow_of_exponent_le hY (by norm_num : (3/2:ℝ)≤(7:ℝ)*(1/2))).trans h0
  have hy : Y^((11/2):ℝ)≤X := by
    apply (Real.rpow_le_rpow_of_exponent_le hY (by norm_num : (11/2:ℝ)≤7)).trans
    simpa only [Real.rpow_ofNat] using hYX
  have h0 : X^(3:ℝ)*Y^(-3:ℝ)≤X^((7/2):ℝ)*Y^(-(9/2):ℝ) := by
    calc
      _ = (X^(3:ℝ)*Y^(-(9/2):ℝ))*Y^((3/2):ℝ) := by
        rw [mul_assoc,← Real.rpow_add hYp]
        norm_num
      _ ≤ (X^(3:ℝ)*Y^(-(9/2):ℝ))*X^((1/2):ℝ) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by
        rw [mul_right_comm,← Real.rpow_add hXp]
        norm_num
  have h1 : X^((5/2):ℝ)*Y≤X^((7/2):ℝ)*Y^(-(9/2):ℝ) := by
    calc
      _ = (X^((5/2):ℝ)*Y^(-(9/2):ℝ))*Y^((11/2):ℝ) := by
        rw [mul_assoc,← Real.rpow_add hYp]
        norm_num
      _ ≤ (X^((5/2):ℝ)*Y^(-(9/2):ℝ))*X :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      _ = _ := by
        calc
          _ = (X^((5/2):ℝ)*X^(1:ℝ))*Y^(-(9/2):ℝ) := by rw [Real.rpow_one]; ring
          _ = _ := by rw [← Real.rpow_add hXp]; norm_num
  linarith only [h0,h1]

theorem mixed_major_scale_bound (X Y L ε : ℝ)
    (hX : 1≤X) (hY : 1≤Y) (hL : 1≤L) (hYX : Y^7≤X) (hε : 0≤ε) :
    (X/Y^3)*X*X^(ε/2)*Y*((X/Y)^3)⁻¹*
      ((X/Y)^4+(L*X)^((7/2:ℝ)+ε/2)) ≤
      (2*L^((7/2:ℝ)+ε/2))*X^((7/2:ℝ)+ε)*Y^(-(9/2):ℝ) := by
  have hXp : 0<X := by linarith
  have hYp : 0<Y := by linarith
  have hLp : 0<L := by linarith
  have hLpow : 1≤L^((7/2:ℝ)+ε/2) := Real.one_le_rpow hL (by linarith)
  rw [mixed_major_scale_polynomial X Y L ε hXp hYp hLp]
  have hfirst : X^(3+ε/2)*Y^(-3:ℝ)≤X^ε*(X^(3:ℝ)*Y^(-3:ℝ)) := by
    apply (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hX (show 3+ε/2≤3+ε by linarith))
      (Real.rpow_nonneg hYp.le _)).trans_eq
    rw [Real.rpow_add hXp]
    ring
  have hsecond : X^((5/2:ℝ)+ε)*Y=X^ε*(X^((5/2):ℝ)*Y) := by
    rw [Real.rpow_add hXp]
    ring
  have hsum : X^(3+ε/2)*Y^(-3:ℝ)+X^((5/2:ℝ)+ε)*Y ≤
      2*X^((7/2:ℝ)+ε)*Y^(-(9/2):ℝ) := by
    calc
      _ ≤ X^ε*(X^(3:ℝ)*Y^(-3:ℝ)+X^((5/2):ℝ)*Y) := by rw [mul_add,← hsecond]; exact add_le_add_right hfirst _
      _ ≤ X^ε*(2*X^((7/2):ℝ)*Y^(-(9/2):ℝ)) :=
        mul_le_mul_of_nonneg_left (mixed_major_monomials_domination X Y hX hY hYX)
          (Real.rpow_nonneg hXp.le _)
      _ = _ := by rw [Real.rpow_add hXp]; ring
  calc
    _ ≤ L^((7/2:ℝ)+ε/2)*(X^(3+ε/2)*Y^(-3:ℝ)+X^((5/2:ℝ)+ε)*Y) := by
      have hh := le_mul_of_one_le_left (show 0≤X^(3+ε/2)*Y^(-3:ℝ) by positivity) hLpow
      exact (add_le_add_right hh _).trans_eq (by ring)
    _ ≤ L^((7/2:ℝ)+ε/2)*(2*X^((7/2:ℝ)+ε)*Y^(-(9/2):ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hLp.le _)
    _ = _ := by ring

#print axioms mixed_major_scale_polynomial
#print axioms mixed_major_monomials_domination
#print axioms mixed_major_scale_bound
end WaringSiegel.WSL4
