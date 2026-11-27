import WaringSiegel.WSL4MajorPowerCutoff

/-! # Quantitative relative errors for the auxiliary power cutoff -/
noncomputable section
set_option maxHeartbeats 1100000
open Filter Topology
namespace WaringSiegel.WSL4

theorem auxiliary_cutoff_five_fourths (X : ℝ) (hX : 0<X) :
    (X^((4:ℝ)/5))^((5:ℝ)/4)=X := by
  rw [← Real.rpow_mul hX.le]
  norm_num

theorem auxiliary_bounded_power_ratio (X Y δ r : ℝ) (hX : 0<X) (hY : 0≤Y)
    (hYX : Y≤X^δ) (n : ℕ) :
    Y^n/X^r≤X^(δ*(n:ℝ)-r) := by
  rw [Real.rpow_sub hX,Real.rpow_mul_natCast hX.le]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hY hYX n) (Real.rpow_nonneg hX.le r)

theorem auxiliary_cutoff_ratio_le (X Y δ : ℝ) (hX : 0<X) (hYX : Y≤X^δ) :
    Y*X^((4:ℝ)/5)/X≤X^(δ-1/5) := by
  calc
    _ ≤ X^δ*X^((4:ℝ)/5)/X := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hYX (Real.rpow_nonneg hX.le _)) hX.le
    _ = _ := by
      rw [← Real.rpow_add hX,← Real.rpow_sub_one hX.ne']
      congr 1
      ring

theorem auxiliary_cutoff_poisson_relative_le (X Y δ : ℝ) (hX : 0<X)
    (hY : 0≤Y) (hYX : Y≤X^δ) (N : ℕ) :
    X^3*(Y*X^((4:ℝ)/5)/X)^N≤X^(3+(N:ℝ)*(δ-1/5)) := by
  calc
    _ ≤ X^3*(X^(δ-1/5))^N := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (auxiliary_cutoff_ratio_le X Y δ hX hYX) N)
      (pow_nonneg hX.le _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hX.le,← Real.rpow_natCast X 3,← Real.rpow_add hX]
      congr 1
      ring

theorem auxiliary_relative_error_le
    (X Y δ C D E : ℝ) (hX : 0<X) (hY : 0≤Y) (hYX : Y≤X^δ)
    (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (N : ℕ) :
    C*X^3*(Y*X^((4:ℝ)/5)/X)^N + D*Y^2/(X^((4:ℝ)/5))^((5:ℝ)/4) +
      E*Y^4*(1/(X^((4:ℝ)/5))^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) ≤
      C*X^(3+(N:ℝ)*(δ-1/5)) + D*X^(2*δ-1) +
        E*(X^(4*δ-1)+X^(12*δ-5/4)) := by
  rw [auxiliary_cutoff_five_fourths X hX]
  have h2 := auxiliary_bounded_power_ratio X Y δ 1 hX hY hYX 2
  have h4 := auxiliary_bounded_power_ratio X Y δ 1 hX hY hYX 4
  have h12 := auxiliary_bounded_power_ratio X Y δ (5/4) hX hY hYX 12
  norm_num only [Real.rpow_one,Nat.cast_ofNat] at h2 h4 h12
  have he : E*Y^4*(1/X+Y^8/X^((5:ℝ)/4))=E*(Y^4/X+Y^12/X^((5:ℝ)/4)) := by ring
  rw [he]
  apply add_le_add
  · apply add_le_add
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (auxiliary_cutoff_poisson_relative_le X Y δ hX hY hYX N) hC
    · simpa only [mul_div_assoc,mul_comm δ (2:ℝ)] using mul_le_mul_of_nonneg_left h2 hD
  · apply mul_le_mul_of_nonneg_left _ hE
    simpa only [mul_comm δ (4:ℝ),mul_comm δ (12:ℝ)] using add_le_add h4 h12

theorem exists_auxiliary_poisson_order (δ : ℝ) (hδ : δ<1/5) :
    ∃ N : ℕ, 3+(N:ℝ)*(δ-1/5)<0 := by
  obtain ⟨N,hN⟩ := exists_power_cutoff_poisson_order 3 (δ+4/5) (by linarith)
  refine ⟨N,?_⟩
  norm_num only [Nat.cast_ofNat] at hN
  convert hN using 1 <;> ring

theorem auxiliary_relative_majorant_tendsto (δ C D E : ℝ) (hδ : δ<5/48)
    (N : ℕ) (hN : 3+(N:ℝ)*(δ-1/5)<0) :
    Tendsto (fun X : ℝ => C*X^(3+(N:ℝ)*(δ-1/5))+D*X^(2*δ-1)+
      E*(X^(4*δ-1)+X^(12*δ-5/4))) atTop (𝓝 0) := by
  have hpow (r : ℝ) (hr : r<0) : Tendsto (fun X : ℝ => X^r) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hr)
  have h1 := (hpow _ hN).const_mul C
  have h2 := (hpow (2*δ-1) (by linarith)).const_mul D
  have h3 := ((hpow (4*δ-1) (by linarith)).add (hpow (12*δ-5/4) (by linarith))).const_mul E
  simpa only [mul_zero,add_zero] using (h1.add h2).add h3

theorem exists_auxiliary_relative_error_small
    (δ C D E c : ℝ) (hδ : δ<5/48) (hC : 0≤C) (hD : 0≤D) (hE : 0≤E) (hc : 0<c)
    (N : ℕ) (hN : 3+(N:ℝ)*(δ-1/5)<0) :
    ∃ X0 : ℝ, 1≤X0 ∧ ∀ X Y : ℝ, X0<X → 0≤Y → Y≤X^δ →
      Y*X^((4:ℝ)/5)/X≤1 ∧
      C*X^3*(Y*X^((4:ℝ)/5)/X)^N + D*Y^2/(X^((4:ℝ)/5))^((5:ℝ)/4) +
        E*Y^4*(1/(X^((4:ℝ)/5))^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) < c := by
  have hlim := auxiliary_relative_majorant_tendsto δ C D E hδ N hN
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlim.eventually_lt_const hc)
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro X Y hX hY hYX
  have hX1 : 1≤X := (le_max_left _ _).trans hX.le
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX1
  refine ⟨(auxiliary_cutoff_ratio_le X Y δ hX0 hYX).trans ?_,?_⟩
  · simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hX1
      (show δ-1/5≤0 by linarith)
  · exact (auxiliary_relative_error_le X Y δ C D E hX0 hY hYX hC hD hE N).trans_lt
      (hM X ((le_max_right _ _).trans hX.le))

#print axioms auxiliary_relative_error_le
#print axioms exists_auxiliary_relative_error_small
end WaringSiegel.WSL4
