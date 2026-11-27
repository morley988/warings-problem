import WaringEnvelope.RealProfile
import WaringEnvelope.TailMonotonicity

/-! # Real interpretation of terminal prices in the scalar menus -/
noncomputable section
namespace WaringEnvelope

def length (m : ℕ) : ℝ := (U:ℝ)*m/(V*B)

def fee (c : Config) : ℕ × ℕ :=
  if 7*(10*c.root)≤20*21 then (7,20) else (21,10*c.root)

private theorem scaled_ceil (a b : ℕ) (hb : 0<b) :
    (a:ℝ)/b ≤ (ceilDiv (a*D) b : ℝ)/D := by
  have hd : (0:ℝ)<D := by norm_num [D]
  have hh := real_le_ceilDiv (a*D) b hb
  push_cast at hh
  apply (le_div_iff₀ hd).2
  calc
    _ = (a:ℝ)*D/b := by ring
    _ ≤ _ := hh

private theorem rebate_sound (m : ℕ) (hm : 0<m) :
    (((2*D*B*V/(U*m):ℕ):ℝ)/D) ≤ 2/length m := by
  have hU : (0:ℝ)<U := by norm_num [U]
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hD : (0:ℝ)<D := by norm_num [D]
  have hB : (0:ℝ)<B := by norm_num [B]
  have hV : (0:ℝ)<V := by norm_num [V]
  have hh := Nat.cast_div_le (α := ℝ) (m := 2*D*B*V) (n := U*m)
  calc
    _ ≤ ((2*D*B*V:ℕ):ℝ)/(U*m:ℕ)/D := div_le_div_of_nonneg_right hh hD.le
    _ = _ := by push_cast; unfold length; field_simp

/-- For each finite band the true rounded endpoint costs imply the real
logarithmic envelope at every included degree. This form accepts either choice
of the initial height and thus applies to both all-degree certificates. -/
theorem finiteFinal_real_price (c : Config) (s : State) (z₀ bound k : ℕ) (R : ℝ)
    (hc : 0<c.first) (hk : c.first≤k) (hR : R≤(s.cost:ℝ)/D)
    (hlog : validLog (T-z₀) z₀ c.baseLog=true)
    (hf : finiteFinal c s bound=true) :
    2+Real.log (((T-z₀:ℕ):ℝ)/z₀)+R-2/length s.modulus +
      ((fee c).1:ℝ)/(fee c).2+6/k < (bound:ℝ)/D := by
  obtain ⟨a,b,hab⟩ : ∃ a b, fee c=(a,b) := ⟨_,_,Prod.mk.eta.symm⟩
  have hab' := hab
  unfold fee at hab'
  simp only [finiteFinal,hab',Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at hf
  obtain ⟨⟨⟨⟨hne,hm⟩,hb⟩,hdefect⟩,hcharge⟩ := hf
  rw [hab]
  have hD : (0:ℝ)<D := by norm_num [D]
  have hK : (0:ℝ)<c.first := by exact_mod_cast hc
  have hkR : (c.first:ℝ)≤k := by exact_mod_cast hk
  have hlen := rebate_sound _ hm
  have hfee := scaled_ceil a b hb
  have hsix := scaled_ceil 6 c.first hc
  have hsix' : (6:ℝ)/k ≤ (6:ℝ)/c.first := div_le_div_of_nonneg_left (by norm_num) hK hkR
  have hbase := validLog_sound _ _ _ hlog
  have hN : ((2*D+c.baseLog+s.cost+ceilDiv (a*D) b+ceilDiv (6*D) c.first : ℕ):ℝ) <
      ((bound+2*D*B*V/(U*s.modulus):ℕ):ℝ) := by exact_mod_cast hcharge
  have hN' := (div_lt_div_iff_of_pos_right hD).2 hN
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hN'
  simp only [add_div] at hN'
  have htwo : (2:ℝ)*D/D=2 := by field_simp
  rw [htwo] at hN'
  norm_num only [Nat.cast_ofNat] at hsix
  change 2+Real.log (((T-z₀:ℕ):ℝ)/z₀)+R-2/length s.modulus + (a:ℝ)/b+6/k < (bound:ℝ)/D
  linarith only [hbase,hR,hlen,hfee,hsix,hsix',hN']

#print axioms finiteFinal_real_price
end WaringEnvelope
