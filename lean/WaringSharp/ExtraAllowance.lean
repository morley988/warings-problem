import WaringEnvelope.RealCosts

namespace WaringSharp
open WaringEnvelope

theorem extra_variable_allowance (K k : ℕ) (hK : 1≤K) (hk : K≤k) :
    ((6873*D/1000-ceilDiv D K:ℕ):ℝ)/D+1/k≤6873/1000 := by
  have hD : 0<D := by decide
  have hceil : ceilDiv D K≤D := by
    unfold ceilDiv
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hK).2
    have hm := Nat.mul_le_mul_left D hK
    simp only [mul_one] at hm
    rw [Nat.succ_mul]
    omega
  have hbig : D≤6873*D/1000 := by decide
  rw [Nat.cast_sub (hceil.trans hbig)]
  have hK' : (0:ℝ)<K := by exact_mod_cast hK
  have hk' : (K:ℝ)≤k := by exact_mod_cast hk
  have hD' : (0:ℝ)<D := by exact_mod_cast hD
  have hprice := real_le_ceilDiv D K hK
  have hal : 1/(k:ℝ)≤(ceilDiv D K:ℝ)/D := by
    apply le_trans (one_div_le_one_div_of_le hK' hk')
    apply (div_le_div_iff₀ hK' hD').2
    have hh := (div_le_iff₀ hK').mp hprice
    linarith
  rw [sub_div]
  have hbase : ((6873*D/1000:ℕ):ℝ)/D=(6873:ℝ)/1000 := by norm_num [D]
  linarith

#print axioms extra_variable_allowance
end WaringSharp
