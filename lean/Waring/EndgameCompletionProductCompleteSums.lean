import Waring.EndgameCompletionImprimitive
import Mathlib.Data.Fin.Tuple.Basic

/-! # Actual product-variable complete sums and their normalized decay -/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

def productCompleteSum (q k L : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ x : Fin L→ZMod q,ZMod.stdAddChar (a*(∏ i,x i)^k)

def normalizedProductCompleteSum (q k L : ℕ) [NeZero q] (a : ZMod q) : ℝ :=
  ‖productCompleteSum q k L a‖/(q : ℝ)^L

theorem normalizedProductCompleteSum_nonneg (q k L : ℕ) [NeZero q] (a : ZMod q) :
    0≤normalizedProductCompleteSum q k L a := div_nonneg (norm_nonneg _) (by positivity)

theorem productCompleteSum_zero (q k : ℕ) [NeZero q] (a : ZMod q) :
    productCompleteSum q k 0 a=ZMod.stdAddChar a := by
  simp [productCompleteSum]

theorem productCompleteSum_succ (q k L : ℕ) [NeZero q] (a : ZMod q) :
    productCompleteSum q k (L+1) a=∑ x : ZMod q,productCompleteSum q k L (a*x^k) := by
  classical
  unfold productCompleteSum
  rw [← (Fin.consEquiv (fun _ : Fin (L+1)=>ZMod q)).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_pow,mul_assoc]

theorem productCompleteSum_one (q k : ℕ) [NeZero q] (a : ZMod q) :
    productCompleteSum q k 1 a=completeMonomialSumMod q k a := by
  rw [show 1=0+1 by omega,productCompleteSum_succ]
  simp_rw [productCompleteSum_zero]
  rfl

theorem normalizedProductCompleteSum_one (q k : ℕ) [NeZero q] (a : ZMod q) :
    normalizedProductCompleteSum q k 1 a=normalizedCompleteSum q k a := by
  simp only [normalizedProductCompleteSum,productCompleteSum_one,pow_one,normalizedCompleteSum]

theorem normalizedProductCompleteSum_succ_le (q k L : ℕ) [NeZero q] (a : ZMod q) :
    normalizedProductCompleteSum q k (L+1) a≤
      (∑ x : ZMod q,normalizedProductCompleteSum q k L (a*x^k))/(q : ℝ) := by
  unfold normalizedProductCompleteSum
  rw [productCompleteSum_succ]
  calc
    _ ≤ (∑ x : ZMod q,‖productCompleteSum q k L (a*x^k)‖)/(q : ℝ)^(L+1) :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = _ := by simp only [Finset.sum_div,pow_succ,div_div]

theorem gcd_zmod_sum_le (q : ℕ) [NeZero q] :
    (∑ x : ZMod q,(Nat.gcd x.val q : ℝ))≤(q : ℝ)*(q.divisors.card : ℝ) := by
  classical
  have hpoint (x : ZMod q) : (Nat.gcd x.val q : ℝ)≤
      ∑ d∈q.divisors,if d∣x.val then (d : ℝ) else 0 := by
    have hh := Finset.single_le_sum (s := q.divisors)
      (f := fun d : ℕ=>if d∣x.val then (d : ℝ) else 0)
      (fun d _=>by dsimp only; split_ifs <;> positivity)
      (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right x.val q,NeZero.ne q⟩)
    simpa only [if_pos (Nat.gcd_dvd_left x.val q)] using hh
  have hlocal (d : ℕ) (hd : d∈q.divisors) :
      (∑ x : ZMod q,if d∣x.val then (d : ℝ) else 0)=(q : ℝ) := by
    have hdpos := Nat.pos_of_mem_divisors hd
    have hdq := (Nat.mem_divisors.mp hd).1
    have hq : q=d*(q/d) := (Nat.mul_div_cancel' hdq).symm
    have hc := sum_zmod_filter_dvd q d (q/d) hdpos hq (fun _=>(1 : ℂ))
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hc
    have hcr : (((Finset.univ : Finset (ZMod q)).filter (fun x=>d∣x.val)).card : ℝ)=(q/d : ℕ) := by
      exact_mod_cast hc
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,hcr]
    exact_mod_cast Nat.div_mul_cancel hdq
  calc
    _ ≤ ∑ x : ZMod q,∑ d∈q.divisors,if d∣x.val then (d : ℝ) else 0 :=
      Finset.sum_le_sum (fun x _=>hpoint x)
    _ = ∑ d∈q.divisors,∑ x : ZMod q,if d∣x.val then (d : ℝ) else 0 := Finset.sum_comm
    _ = _ := by rw [Finset.sum_congr rfl hlocal]; simp [mul_comm]

/-- The L+1 product factors cost only the L-th power of the divisor count.
The statement retains an arbitrary, possibly imprimitive, coefficient. -/
theorem normalizedProductCompleteSum_divisor_bound (k : ℕ) (hk : 0<k)
    {C ε : ℝ} (hC : 0<C) (hε : 0≤ε)
    (hprimitive : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedCompleteSum q k a≤C*(q : ℝ)^(-1/(k : ℝ)+ε))
    (L q : ℕ) [NeZero q] (a : ZMod q) :
    normalizedProductCompleteSum q k (L+1) a≤
      C*(q : ℝ)^(-1/(k : ℝ)+ε)*(q.divisors.card : ℝ)^L*
        (Nat.gcd a.val q : ℝ)^(1/(k : ℝ)) := by
  induction L generalizing a with
  | zero =>
      simpa only [zero_add,normalizedProductCompleteSum_one,pow_zero,mul_one] using
        normalizedCompleteSum_imprimitive_le_rpow k hε hC hprimitive q a
  | succ L ih =>
      have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
      have hmajor (x : ZMod q) : normalizedProductCompleteSum q k (L+1) (a*x^k)≤
          (C*(q : ℝ)^(-1/(k : ℝ)+ε)*(q.divisors.card : ℝ)^L*
            (Nat.gcd a.val q : ℝ)^(1/(k : ℝ)))*(Nat.gcd x.val q : ℝ) := by
        exact (ih (a*x^k)).trans ((mul_le_mul_of_nonneg_left (gcd_zmod_monomial_rpow_le q k hk a x)
          (by positivity)).trans_eq (by ring))
      calc
        _ ≤ (∑ x : ZMod q,normalizedProductCompleteSum q k (L+1) (a*x^k))/(q : ℝ) :=
          normalizedProductCompleteSum_succ_le q k (L+1) a
        _ ≤ (∑ x : ZMod q,(C*(q : ℝ)^(-1/(k : ℝ)+ε)*(q.divisors.card : ℝ)^L*
            (Nat.gcd a.val q : ℝ)^(1/(k : ℝ)))*(Nat.gcd x.val q : ℝ))/(q : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _=>hmajor x)) hq.le
        _ = (C*(q : ℝ)^(-1/(k : ℝ)+ε)*(q.divisors.card : ℝ)^L*
            (Nat.gcd a.val q : ℝ)^(1/(k : ℝ)))*(∑ x : ZMod q,(Nat.gcd x.val q : ℝ))/(q : ℝ) := by
          rw [← Finset.mul_sum]
        _ ≤ (C*(q : ℝ)^(-1/(k : ℝ)+ε)*(q.divisors.card : ℝ)^L*
            (Nat.gcd a.val q : ℝ)^(1/(k : ℝ)))*((q : ℝ)*(q.divisors.card : ℝ))/(q : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (gcd_zmod_sum_le q) (by positivity)) hq.le
        _ = _ := by rw [pow_succ]; field_simp

theorem normalizedProductCompleteSum_le_rpow_of_recurrence (k : ℕ) (hk : 2≤k)
    (hrec : ∀ (p : ℕ) [Fact p.Prime],PrimePowerRecurrence p k)
    (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedProductCompleteSum q k (L+1) a≤C*(q : ℝ)^(-1/(k : ℝ)+ε) := by
  obtain ⟨A,hA,hprimitive⟩ := normalizedCompleteSum_le_rpow_of_recurrence k hk hrec (half_pos hε)
  obtain ⟨B,hB,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow L (half_pos hε)
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro q _ a
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hb := normalizedProductCompleteSum_divisor_bound k (by omega) hA (half_pos hε).le
    hprimitive L q (a : ZMod q)
  rw [ZMod.val_coe_unit_coprime a,Nat.cast_one,Real.one_rpow,mul_one] at hb
  calc
    _ ≤ A*(q : ℝ)^(-1/(k : ℝ)+ε/2)*(q.divisors.card : ℝ)^L := hb
    _ ≤ A*(q : ℝ)^(-1/(k : ℝ)+ε/2)*(B*(q : ℝ)^(ε/2)) :=
      mul_le_mul_of_nonneg_left (hdiv q (NeZero.pos q)) (by positivity)
    _ = _ := by
      rw [show A*(q : ℝ)^(-1/(k : ℝ)+ε/2)*(B*(q : ℝ)^(ε/2))=
        (A*B)*((q : ℝ)^(-1/(k : ℝ)+ε/2)*(q : ℝ)^(ε/2)) by ring,← Real.rpow_add hq]
      congr 2
      ring

theorem degree8_productCompleteSum_pointwise (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedProductCompleteSum q 8 (L+1) a≤C*(q : ℝ)^(-(1/8 : ℝ)+ε) := by
  have hh := normalizedProductCompleteSum_le_rpow_of_recurrence 8 (by norm_num)
    (fun p hp=>@primePowerRecurrence_eight p hp) L hε
  simpa only [Nat.cast_ofNat,neg_div] using hh

theorem degree9_productCompleteSum_pointwise (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedProductCompleteSum q 9 (L+1) a≤C*(q : ℝ)^(-(1/9 : ℝ)+ε) := by
  have hh := normalizedProductCompleteSum_le_rpow_of_recurrence 9 (by norm_num)
    (fun p hp=>@primePowerRecurrence_nine p hp) L hε
  simpa only [Nat.cast_ofNat,neg_div] using hh

#print axioms gcd_zmod_sum_le
#print axioms degree8_productCompleteSum_pointwise
#print axioms degree9_productCompleteSum_pointwise
end Waring.EndgameCompletion
