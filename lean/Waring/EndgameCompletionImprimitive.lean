import Waring.EndgameCompletionPointwise

/-! # Exact gcd reduction and imprimitive monomial bounds -/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion
open QuadraticModulation

theorem completeMonomialSumMod_multiple (d q k a : ℕ) [NeZero d] [NeZero q] :
    completeMonomialSumMod (d*q) k ((d*a : ℕ) : ZMod (d*q))=
      (d : ℂ)*completeMonomialSumMod q k (a : ZMod q) := by
  have hd : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
  have hleft := completeMonomialSumMod_eq_range (d*q) k ((d*a : ℕ) : ℤ)
  have hright := completeMonomialSumMod_eq_range q k (a : ℤ)
  simp only [Int.cast_natCast] at hleft hright
  rw [hleft]
  have hc : ((d*a : ℕ) : ℝ)/(d*q : ℕ)=(a : ℝ)/q := by
    push_cast
    rw [mul_div_mul_left _ _ hd]
  simp_rw [hc]
  have hper : Function.Periodic (fun y : ℕ=>e ((a : ℝ)/q*(y : ℝ)^k)) q := by
    simpa only [Int.cast_natCast] using rational_monomial_periodic k (a : ℤ) (NeZero.pos q)
  rw [periodic_sum_full_blocks hper,← hright]

theorem normalizedCompleteSum_multiple (d q k a : ℕ) [NeZero d] [NeZero q] :
    normalizedCompleteSum (d*q) k ((d*a : ℕ) : ZMod (d*q))=
      normalizedCompleteSum q k (a : ZMod q) := by
  unfold normalizedCompleteSum
  rw [completeMonomialSumMod_multiple,norm_mul,Complex.norm_natCast,Nat.cast_mul]
  field_simp [show (d : ℝ)≠0 by exact_mod_cast NeZero.ne d]

theorem normalizedCompleteSum_gcd_reduction (q k a : ℕ) [NeZero q]
    [NeZero (q/Nat.gcd a q)] :
    normalizedCompleteSum q k (a : ZMod q)=
      normalizedCompleteSum (q/Nat.gcd a q) k ((a/Nat.gcd a q : ℕ) : ZMod (q/Nat.gcd a q)) := by
  let d := Nat.gcd a q
  let r := q/d
  let b := a/d
  have hd : 0<d := Nat.gcd_pos_of_pos_right _ (NeZero.pos q)
  letI : NeZero d := ⟨hd.ne'⟩
  have hq : q=d*r := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)).symm
  have ha : a=d*b := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)).symm
  calc
    _ = normalizedCompleteSum (d*r) k (a : ZMod (d*r)) :=
      normalizedCompleteSum_nat_congr_modulus q (d*r) k a hq
    _ = normalizedCompleteSum (d*r) k ((d*b : ℕ) : ZMod (d*r)) := by
      exact congrArg (fun z : ℕ=>normalizedCompleteSum (d*r) k (z : ZMod (d*r))) ha
    _ = _ := normalizedCompleteSum_multiple d r k b

theorem normalizedCompleteSum_imprimitive_le_rpow (k : ℕ) {ε C : ℝ}
    (hε : 0≤ε) (hC : 0<C)
    (hprimitive : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedCompleteSum q k a≤C*(q : ℝ)^(-1/(k : ℝ)+ε))
    (q : ℕ) [NeZero q] (a : ZMod q) :
    normalizedCompleteSum q k a≤C*(q : ℝ)^(-1/(k : ℝ)+ε)*
      (Nat.gcd a.val q : ℝ)^(1/(k : ℝ)) := by
  let d := Nat.gcd a.val q
  let r := q/d
  let b := a.val/d
  have hd : 0<d := Nat.gcd_pos_of_pos_right _ (NeZero.pos q)
  have hr : 0<r := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) (Nat.gcd_dvd_right _ _)) hd
  letI : NeZero r := ⟨hr.ne'⟩
  have hb : b.Coprime r := Nat.coprime_div_gcd_div_gcd hd
  let u : (ZMod r)ˣ := ZMod.unitOfCoprime b hb
  have hu : (u : ZMod r)=(b : ZMod r) := ZMod.coe_unitOfCoprime _ _
  have he := normalizedCompleteSum_gcd_reduction q k a.val
  rw [ZMod.natCast_zmod_val] at he
  rw [he,← hu]
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hd1 : (1 : ℝ)≤d := by exact_mod_cast hd
  have hq : (q : ℝ)=(d : ℝ)*(r : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a.val q)).symm
  calc
    _ ≤ C*(r : ℝ)^(-1/(k : ℝ)+ε) := hprimitive r u
    _ ≤ (C*(r : ℝ)^(-1/(k : ℝ)+ε))*(d : ℝ)^ε :=
      le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hd1 hε)
    _ = _ := by
      change _=C*(q : ℝ)^(-1/(k : ℝ)+ε)*(d : ℝ)^(1/(k : ℝ))
      rw [hq,Real.mul_rpow hdR.le hrR.le]
      have hpowers : (d : ℝ)^(-1/(k : ℝ)+ε)*(d : ℝ)^(1/(k : ℝ))=(d : ℝ)^ε := by
        rw [← Real.rpow_add hdR]
        congr 1
        ring
      calc
        _ = C*(r : ℝ)^(-1/(k : ℝ)+ε)*
            ((d : ℝ)^(-1/(k : ℝ)+ε)*(d : ℝ)^(1/(k : ℝ))) := by rw [hpowers]
        _ = _ := by ring

theorem gcd_zmod_monomial_power_le (q k : ℕ) [NeZero q] (a x : ZMod q) :
    Nat.gcd (a*x^k).val q≤Nat.gcd a.val q*(Nat.gcd x.val q)^k := by
  have hphase : a*x^k=((a.val*x.val^k : ℕ) : ZMod q) := by
    rw [Nat.cast_mul,Nat.cast_pow,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  rw [hphase,ZMod.val_natCast,← Nat.gcd_rec,Nat.gcd_comm q]
  have hd : Nat.gcd (a.val*x.val^k) q∣Nat.gcd a.val q*(Nat.gcd x.val q)^k := by
    have hm : Nat.gcd (a.val*x.val^k) q∣Nat.gcd a.val q*Nat.gcd (x.val^k) q := by
      simpa only [Nat.gcd_comm] using gcd_mul_dvd_mul_gcd q a.val (x.val^k)
    exact hm.trans (Nat.mul_dvd_mul_left _ gcd_pow_left_dvd_pow_gcd)
  exact Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_right _ (NeZero.pos q))
    (pow_pos (Nat.gcd_pos_of_pos_right _ (NeZero.pos q)) k)) hd

theorem gcd_zmod_monomial_rpow_le (q k : ℕ) [NeZero q] (hk : 0<k) (a x : ZMod q) :
    (Nat.gcd (a*x^k).val q : ℝ)^(1/(k : ℝ))≤
      (Nat.gcd a.val q : ℝ)^(1/(k : ℝ))*(Nat.gcd x.val q : ℝ) := by
  have hkR : (k : ℝ)≠0 := by exact_mod_cast hk.ne'
  have he : ((Nat.gcd a.val q : ℝ)*(Nat.gcd x.val q : ℝ)^k)^(1/(k : ℝ))=
      (Nat.gcd a.val q : ℝ)^(1/(k : ℝ))*(Nat.gcd x.val q : ℝ) := by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_natCast_mul (Nat.cast_nonneg _),mul_one_div_cancel hkR,Real.rpow_one]
  exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast gcd_zmod_monomial_power_le q k a x)
    (by positivity : (0 : ℝ)≤1/(k : ℝ))).trans_eq he

#print axioms normalizedCompleteSum_gcd_reduction
#print axioms normalizedCompleteSum_imprimitive_le_rpow
#print axioms gcd_zmod_monomial_rpow_le
end Waring.EndgameCompletion
