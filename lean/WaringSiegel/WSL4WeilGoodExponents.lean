import WaringSiegel.WSL3CubicKappaLocal

/-! # Exponent bookkeeping for the actual three-step cubic local bound -/
noncomputable section
namespace WaringSiegel.WSL4Weil

def cubicGoodExponent (r : ℕ) : ℝ := 2*((r/3 : ℕ) : ℝ)+((r%3 : ℕ) : ℝ)/2
def cubicGoodMajorant (q : ℝ) (r : ℕ) : ℝ := 2*q^(cubicGoodExponent r)

theorem cubicGoodExponent_add_three (r : ℕ) :
    cubicGoodExponent (r+3)=cubicGoodExponent r+2 := by
  have hd : (r+3)/3=r/3+1 := by omega
  have hm : (r+3)%3=r%3 := by omega
  simp only [cubicGoodExponent,hd,hm,Nat.cast_add,Nat.cast_one]
  ring

theorem cubicGoodExponent_ceil_half (r : ℕ) (hr : 2≤r) :
    ((r-r/2 : ℕ) : ℝ) ≤ cubicGoodExponent r := by
  have hh : 2*(r-r/2) ≤ 4*(r/3)+r%3 := by omega
  have hh' : (2:ℝ)*((r-r/2 : ℕ) : ℝ) ≤ 4*((r/3 : ℕ) : ℝ)+((r%3 : ℕ) : ℝ) := by
    exact_mod_cast hh
  unfold cubicGoodExponent
  linarith

theorem cubicGoodMajorant_add_three (q : ℝ) (hq : 0<q) (r : ℕ) :
    cubicGoodMajorant q (r+3)=q^2*cubicGoodMajorant q r := by
  rw [cubicGoodMajorant,cubicGoodExponent_add_three,Real.rpow_add hq]
  norm_num [cubicGoodMajorant]
  ring

theorem cubicGoodExponent_succ_formula (e : ℕ) :
    cubicGoodExponent (e+1)=(e+1 : ℕ)-(e/3 : ℕ)-(if e%3=0 then (1/2:ℝ) else 1) := by
  have hm : e%3<3 := Nat.mod_lt _ (by decide)
  have he : (e : ℝ)=3*((e/3 : ℕ) : ℝ)+((e%3 : ℕ) : ℝ) := by
    exact_mod_cast (show e=3*(e/3)+e%3 by omega)
  by_cases h0 : e%3=0
  · have hd : (e+1)/3=e/3 := by omega
    have hr : (e+1)%3=1 := by omega
    simp only [cubicGoodExponent,hd,hr,h0,if_true,Nat.cast_one,Nat.cast_add]
    simp only [h0,Nat.cast_zero] at he
    linarith
  · have h1or2 : e%3=1 ∨ e%3=2 := by omega
    rcases h1or2 with h1 | h2
    · have hd : (e+1)/3=e/3 := by omega
      have hr : (e+1)%3=2 := by omega
      simp only [cubicGoodExponent,hd,hr,if_neg h0,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
      simp only [h1,Nat.cast_one] at he
      linarith
    · have hd : (e+1)/3=e/3+1 := by omega
      have hr : (e+1)%3=0 := by omega
      simp only [cubicGoodExponent,hd,hr,if_neg h0,Nat.cast_zero,Nat.cast_add,Nat.cast_one]
      simp only [h2,Nat.cast_ofNat] at he
      linarith

theorem cubicGoodMajorant_eq_norm_kappa (q C : ℝ) (hq : 0<q) (e : ℕ) :
    cubicGoodMajorant q (e+1)=q^(e+1)*cubicKappaLocal q C true e := by
  unfold cubicGoodMajorant cubicKappaLocal
  simp only [Bool.true_eq,if_true]
  rw [mul_left_comm,← Real.rpow_natCast q (e+1),← Real.rpow_add hq]
  congr 2
  rw [cubicGoodExponent_succ_formula]
  push_cast
  ring

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.cubicGoodMajorant_eq_norm_kappa
