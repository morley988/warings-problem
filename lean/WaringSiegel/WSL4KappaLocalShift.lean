import WaringSiegel.WSL4ConductorMultiplier

/-! # Uniform local kappa ratios under bounded conductor loss -/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local

def cubicKappaAt (q C : ℝ) (good : Bool) (e : ℕ) : ℝ :=
  if e=0 then 1 else cubicKappaLocal q C good (e-1)

@[simp] theorem cubicKappaAt_zero (q C : ℝ) (good : Bool) : cubicKappaAt q C good 0=1 := by
  simp [cubicKappaAt]

theorem cubicKappaAt_nonneg (q C : ℝ) (good : Bool) (e : ℕ)
    (hq : 0≤q) (hC : 0≤C) : 0≤cubicKappaAt q C good e := by
  unfold cubicKappaAt
  split_ifs
  · exact zero_le_one
  · exact cubicKappaLocal_nonneg q C good (e-1) hq hC

theorem cubicKappaAt_bad (q C : ℝ) (e : ℕ) :
    cubicKappaAt q C false e=if e=0 then 1 else C*q^(-(e:ℝ)/3) := by
  unfold cubicKappaAt
  split_ifs with he
  · rfl
  · simp only [cubicKappaLocal,Bool.false_eq_true,if_false,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]

theorem cubicKappaAt_bad_bounded_loss (q C : ℝ) (hq : 1≤q) (hC : 0<C)
    (e f t : ℕ) (hfe : f≤e) (het : e≤f+t) :
    cubicKappaAt q C false f≤
      (max 1 C⁻¹*q^((t:ℝ)/3))*cubicKappaAt q C false e := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hM : 1≤max 1 C⁻¹ := le_max_left _ _
  have hM0 : 0≤max 1 C⁻¹ := zero_le_one.trans hM
  have ht : 1≤q^((t:ℝ)/3) := Real.one_le_rpow hq (by positivity)
  have hMC : 1≤max 1 C⁻¹*C := by
    have h := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) C⁻¹) hC.le
    simpa only [inv_mul_cancel₀ hC.ne'] using h
  rw [cubicKappaAt_bad,cubicKappaAt_bad]
  by_cases he : e=0
  · have hf : f=0 := by omega
    simp only [he,hf,if_true,mul_one]
    exact one_le_mul_of_one_le_of_one_le hM ht
  · simp only [he,if_false]
    by_cases hf : f=0
    · simp only [hf,if_true]
      have hte : (e:ℝ)≤t := by exact_mod_cast (show e≤t by omega)
      have hp : 1≤q^((t:ℝ)/3-(e:ℝ)/3) := Real.one_le_rpow hq (by linarith)
      calc
        1≤(max 1 C⁻¹*C)*q^((t:ℝ)/3-(e:ℝ)/3) := one_le_mul_of_one_le_of_one_le hMC hp
        _=(max 1 C⁻¹*q^((t:ℝ)/3))*(C*q^(-(e:ℝ)/3)) := by
          rw [sub_eq_add_neg,Real.rpow_add hq0]
          ring
    · simp only [hf,if_false]
      have heR : (e:ℝ)≤(f:ℝ)+(t:ℝ) := by exact_mod_cast het
      have hp : q^(-(f:ℝ)/3)≤q^((t:ℝ)/3)*q^(-(e:ℝ)/3) := by
        rw [← Real.rpow_add hq0]
        exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
      have hp0 : 0≤C*(q^((t:ℝ)/3)*q^(-(e:ℝ)/3)) := by positivity
      calc
        C*q^(-(f:ℝ)/3)≤C*(q^((t:ℝ)/3)*q^(-(e:ℝ)/3)) := mul_le_mul_of_nonneg_left hp hC.le
        _≤max 1 C⁻¹*(C*(q^((t:ℝ)/3)*q^(-(e:ℝ)/3))) := le_mul_of_one_le_left hp0 hM
        _=(max 1 C⁻¹*q^((t:ℝ)/3))*(C*q^(-(e:ℝ)/3)) := by ring

#print axioms cubicKappaAt_bad_bounded_loss
end WaringSiegel.WSL4Local
