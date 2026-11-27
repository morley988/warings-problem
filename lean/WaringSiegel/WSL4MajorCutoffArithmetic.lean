import WaringSiegel.WSL4MajorScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # A growing square-root conductor cutoff and its quantitative errors -/
noncomputable section
set_option maxHeartbeats 800000
open Filter Topology
open scoped NumberField Classical
namespace WaringSiegel.WSL4

theorem sqrt_cutoff_bounds (X : ℝ) (hX : 1≤X) :
    1≤Real.sqrt X ∧ Real.sqrt X≤X := by
  refine ⟨Real.one_le_sqrt.mpr hX,?_⟩
  exact Real.sqrt_le_iff.mpr ⟨le_trans zero_le_one hX,by nlinarith⟩

theorem sqrt_cutoff_poisson_error (X : ℝ) (hX : 1≤X) (k n : ℕ) :
    X^n*(Real.sqrt X/X)^(2*(k+1))*(1+Real.sqrt X/X) ≤
      X^((n:ℝ)-k)*(2/X) := by
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hr0 : 0≤Real.sqrt X/X := div_nonneg (Real.sqrt_nonneg X) hX0.le
  have hr : Real.sqrt X/X≤1 := (div_le_one hX0).mpr (sqrt_cutoff_bounds X hX).2
  have hs : (Real.sqrt X/X)^2=X⁻¹ := by
    rw [div_pow,Real.sq_sqrt hX0.le]
    field_simp [hX0.ne']
  have he : X^n*(Real.sqrt X/X)^(2*(k+1)) = X^((n:ℝ)-k-1) := by
    rw [pow_mul,hs,inv_pow]
    have hexp : (n:ℝ)-k-1=(n:ℝ)-((k+1:ℕ):ℝ) := by push_cast; ring
    rw [hexp,Real.rpow_sub hX0,Real.rpow_natCast,Real.rpow_natCast,div_eq_mul_inv]
  calc
    _ ≤ X^n*(Real.sqrt X/X)^(2*(k+1))*2 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (pow_nonneg hX0.le _) (pow_nonneg hr0 _))
    _ = X^((n:ℝ)-k)*(2/X) := by rw [he,Real.rpow_sub_one hX0.ne']; ring

theorem sqrt_cutoff_rpow (X δ : ℝ) (hX : 0≤X) :
    (Real.sqrt X)^δ=X^(δ/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hX]
  congr 1
  ring

theorem sqrt_cutoff_separated (d k : ℕ) (hk : 2≤k) (a X : ℝ)
    (ha : 0<a) (hX : 1≤X) (hlarge : (2:ℝ)^d/a<X) :
    (2:ℝ)^d*(Real.sqrt X)^2<a*X^k := by
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  rw [Real.sq_sqrt hX0.le]
  have hp : X^2≤X^k := pow_le_pow_right₀ hX hk
  have hc : (2:ℝ)^d<a*X := by
    simpa only [mul_comm] using (div_lt_iff₀ ha).mp hlarge
  calc
    _ < (a*X)*X := mul_lt_mul_of_pos_right hc hX0
    _ = a*X^2 := by ring
    _ ≤ a*X^k := mul_le_mul_of_nonneg_left hp ha.le

theorem exists_sqrt_cutoff_relative_error_small (A B δ c : ℝ)
    (hδ : 0<δ) (hc : 0<c) :
    ∃ X0 : ℝ, 1≤X0 ∧ ∀ X : ℝ, X0<X → A/X+B/X^(δ/2)<c := by
  have hlim : Tendsto (fun X : ℝ => A/X+B/X^(δ/2)) atTop (𝓝 0) := by
    have h1 := (tendsto_id : Tendsto (fun X : ℝ => X) atTop atTop).const_div_atTop A
    have h2 := (tendsto_rpow_atTop (show 0<δ/2 by positivity)).const_div_atTop B
    simpa only [add_zero] using h1.add h2
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hc)
  refine ⟨max 1 N,le_max_left _ _,fun X hX => ?_⟩
  exact hN X ((le_max_right _ _).trans hX.le)

#print axioms sqrt_cutoff_poisson_error
#print axioms sqrt_cutoff_separated
#print axioms exists_sqrt_cutoff_relative_error_small
end WaringSiegel.WSL4
