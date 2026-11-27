import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # All degrees above the square-root cap -/
noncomputable section
namespace WaringEnvelope

/-- The cap correction is maximal at the first degree of the last band. -/
theorem log_log_div_sqrt_antitone {K k A d : ℝ} (hK : 1≤K) (hk : K≤k)
    (hA : 0<A) (hd : 2≤d) (hbase : Real.exp 1≤A*(Real.log K+d)) :
    Real.log (A*(Real.log k+d))/Real.sqrt k ≤
      Real.log (A*(Real.log K+d))/Real.sqrt K := by
  have hKp : 0<K := zero_lt_one.trans_le hK
  have hkp : 0<k := hKp.trans_le hk
  have hsk : 0<Real.sqrt k := Real.sqrt_pos.2 hkp
  have hsK : 0<Real.sqrt K := Real.sqrt_pos.2 hKp
  let t := Real.sqrt k/Real.sqrt K
  have ht : 1≤t := by
    apply (le_div_iff₀ hsK).2
    simpa using Real.sqrt_le_sqrt hk
  have htpos := zero_lt_one.trans_le ht
  let L := Real.log K+d
  have hL : 2≤L := by dsimp [L]; linarith [Real.log_nonneg hK]
  have hLpos : 0<L := by linarith
  have hcapital : 1≤Real.log (A*L) := (Real.le_log_iff_exp_le (mul_pos hA hLpos)).2 hbase
  have hlogt : 2*Real.log t = Real.log k-Real.log K := by
    dsimp [t]
    rw [Real.log_div hsk.ne' hsK.ne',Real.log_sqrt hkp.le,Real.log_sqrt hKp.le]
    ring
  have htl := Real.log_le_sub_one_of_pos htpos
  let X := (Real.log k+d)/L
  have hkL : 0<Real.log k+d := by linarith [Real.log_nonneg (hK.trans hk)]
  have hXp : 0<X := div_pos hkL hLpos
  have hX : X-1 ≤ t-1 := by
    have hmul := mul_le_mul_of_nonneg_right hL (sub_nonneg.mpr ht)
    have hh : Real.log k+d ≤ t*L := by
      dsimp [L] at hmul ⊢
      linarith
    dsimp [X]
    linarith [(div_le_iff₀ hLpos).2 hh]
  have hXeq : A*(Real.log k+d)=(A*L)*X := by dsimp [X]; field_simp
  have hlogs : Real.log (A*(Real.log k+d)) ≤ t*Real.log (A*L) := by
    rw [hXeq,Real.log_mul (mul_pos hA hLpos).ne' hXp.ne']
    have hql := (Real.log_le_sub_one_of_pos hXp).trans hX
    have hmono := mul_le_mul_of_nonneg_left hcapital (sub_nonneg.mpr ht)
    linarith
  have hfit := (div_le_iff₀ hsk).2 (show Real.log (A*(Real.log k+d))≤
      Real.log (A*(Real.log K+d))/Real.sqrt K*Real.sqrt k by
    calc
      _ ≤ _ := hlogs
      _ = _ := by dsimp [t,L]; ring)
  exact hfit

#print axioms log_log_div_sqrt_antitone
end WaringEnvelope
