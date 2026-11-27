import WaringSiegel.WSL4MajorCutoffArithmetic

/-! # Power conductor cutoffs with arbitrarily small fixed exponent loss -/
noncomputable section
set_option maxHeartbeats 1000000
open Filter Topology
namespace WaringSiegel.WSL4

theorem exists_power_cutoff_poisson_order (k : ℕ) (a : ℝ) (ha : a<1) :
    ∃ N : ℕ, (k:ℝ)+(N:ℝ)*(a-1)<0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((k:ℝ)/(1-a))
  refine ⟨N,?_⟩
  have h := (div_lt_iff₀ (sub_pos.mpr ha)).mp hN
  nlinarith

theorem power_cutoff_ratio (X Q a : ℝ) (hX : 0<X) :
    Q*X^a/X=Q*X^(a-1) := by
  rw [Real.rpow_sub_one hX.ne']
  ring

theorem power_cutoff_poisson_factor (X Q a : ℝ) (hX : 0<X) (k n N : ℕ) :
    X^n*(Q*X^a/X)^N*(1+Q*X^a/X) =
      X^((n:ℝ)-k)*(Q^N*X^((k:ℝ)+(N:ℝ)*(a-1))*(1+Q*X^(a-1))) := by
  simp only [power_cutoff_ratio X Q a hX]
  rw [mul_pow,← Real.rpow_mul_natCast hX.le]
  have he : X^n*X^((a-1)*(N:ℝ))=
      X^((n:ℝ)-k)*X^((k:ℝ)+(N:ℝ)*(a-1)) := by
    rw [← Real.rpow_natCast X n,← Real.rpow_add hX,← Real.rpow_add hX]
    congr 1
    ring
  calc
    _ = Q^N*(X^n*X^((a-1)*(N:ℝ)))*(1+Q*X^(a-1)) := by ring
    _ = _ := by rw [he]; ring

theorem power_cutoff_separated (d k : ℕ) (hk : 3≤k) (v X L : ℝ)
    (hv : 0<v) (hX : 1≤X) (hL0 : 0≤L) (hLX : L≤X)
    (hlarge : (2:ℝ)^d/v<X) :
    (2:ℝ)^d*L^2<v*X^k := by
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hpow : X^3≤X^k := pow_le_pow_right₀ hX hk
  have hcoef : (2:ℝ)^d<v*X := by
    simpa only [mul_comm] using (div_lt_iff₀ hv).mp hlarge
  calc
    _ ≤ (2:ℝ)^d*X^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLX 2) (by positivity)
    _ < (v*X)*X^2 := mul_lt_mul_of_pos_right hcoef (pow_pos hX0 2)
    _ = v*X^3 := by ring
    _ ≤ v*X^k := mul_le_mul_of_nonneg_left hpow hv.le

theorem power_cutoff_relative_error_tendsto (k N : ℕ) (Q a δ η C D E : ℝ)
    (hQ : 0<Q) (ha0 : 0<a) (ha1 : a<1) (hδ : 0<δ) (hη : 0<η)
    (hN : (k:ℝ)+(N:ℝ)*(a-1)<0) :
    Tendsto (fun X : ℝ =>
      C*(Q^N*X^((k:ℝ)+(N:ℝ)*(a-1))*(1+Q*X^(a-1)))+
      D/(Q*X^a)^δ+E/X^η) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun X : ℝ => X^(a-1)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (show 0< -(a-1) by linarith)
  have hpow : Tendsto (fun X : ℝ => X^((k:ℝ)+(N:ℝ)*(a-1))) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hN)
  have hfirst : Tendsto (fun X : ℝ =>
      C*(Q^N*X^((k:ℝ)+(N:ℝ)*(a-1))*(1+Q*X^(a-1)))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using ((hpow.const_mul (Q^N)).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).add
        (hsmall.const_mul Q))).const_mul C
  have hden := (tendsto_rpow_atTop hδ).comp
    (Filter.Tendsto.const_mul_atTop hQ (tendsto_rpow_atTop ha0))
  have hsecond := hden.const_div_atTop D
  have hthird := (tendsto_rpow_atTop hη).const_div_atTop E
  simpa only [mul_zero,zero_mul,add_zero] using (hfirst.add hsecond).add hthird

theorem exists_power_cutoff_relative_error_small (k N : ℕ) (Q a δ η C D E c : ℝ)
    (hQ : 1≤Q) (ha0 : 0<a) (ha1 : a<1) (hδ : 0<δ) (hη : 0<η)
    (hN : (k:ℝ)+(N:ℝ)*(a-1)<0) (hc : 0<c) :
    ∃ X0 : ℝ, 1≤X0 ∧ ∀ X : ℝ, X0<X →
      1≤Q*X^a ∧ Q*X^a≤X ∧
      C*(Q^N*X^((k:ℝ)+(N:ℝ)*(a-1))*(1+Q*X^(a-1)))+
        D/(Q*X^a)^δ+E/X^η<c := by
  have hQ0 : 0<Q := lt_of_lt_of_le zero_lt_one hQ
  have hlim := power_cutoff_relative_error_tendsto k N Q a δ η C D E hQ0 ha0 ha1 hδ hη hN
  have hsmall : Tendsto (fun X : ℝ => Q*X^(a-1)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_neg] using
      (tendsto_rpow_neg_atTop (show 0< -(a-1) by linarith)).const_mul Q
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((hlim.eventually_lt_const hc).and (hsmall.eventually_lt_const zero_lt_one))
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro X hX
  have hX1 : 1≤X := (le_max_left _ _).trans hX.le
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX1
  obtain ⟨herr,hratio⟩ := hM X ((le_max_right _ _).trans hX.le)
  refine ⟨one_le_mul_of_one_le_of_one_le hQ (Real.one_le_rpow hX1 ha0.le),?_,herr⟩
  apply (div_le_one hX0).mp
  rw [power_cutoff_ratio X Q a hX0]
  exact hratio.le

#print axioms power_cutoff_poisson_factor
#print axioms exists_power_cutoff_relative_error_small
end WaringSiegel.WSL4
