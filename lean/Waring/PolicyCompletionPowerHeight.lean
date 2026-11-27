import Waring.PolicyCompletionPowerClasses

/-!
# The final weighted power-height resummation in VW95 Lemma4.3

The local conductor is V/j^d, so a matched rational has the same full
conductor V for every j. The j^(-2) weights and exact power-divisor classes
therefore give the terminal exponent 2/d. For degree d=2k this is the
source's basic 1/k height saving.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionPowerHeight
open RationalHeight PolicyCompletionMultiplierHeight PolicyCompletionLinearRootSampling
open PolicyCompletionPowerClasses

theorem power_short_match {d j : ℕ} (hd : 3≤d) (hj : 0<j)
    {V Y α : ℝ} (hV : 0<V) (hY : 0<Y) (r s : ℚ)
    (hs : cost (V/(j : ℝ)^d) (α*(j : ℝ)^d) s=
      height (V/(j : ℝ)^d) (α*(j : ℝ)^d))
    (hshort : height (V/(j : ℝ)^d) (α*(j : ℝ)^d)<(Y/(j : ℝ))^3)
    (hsmall : Y^d*error α r+(r.den : ℝ)*Y^d/V<1) : ScaledMatch r s (j^d) := by
  have hjR : (0 : ℝ)<j := by exact_mod_cast hj
  have hjY : (j : ℝ)<Y := by
    by_contra h
    have hyj : Y/(j : ℝ)≤1 := (div_le_one hjR).mpr (le_of_not_gt h)
    have hp : (Y/(j : ℝ))^3≤1 := pow_le_one₀ (div_nonneg hY.le hjR.le) hyj
    have hh := one_le_height (V/(j : ℝ)^d) (α*(j : ℝ)^d)
    linarith
  have hfactor : (j : ℝ)^d*(Y/(j : ℝ))^3=Y^3*(j : ℝ)^(d-3) := by
    have hd' : d=(d-3)+3 := by omega
    conv_lhs => rw [hd',pow_add]
    rw [div_pow]
    field_simp
  have hprod : (j : ℝ)^d*(Y/(j : ℝ))^3≤Y^d := by
    rw [hfactor]
    calc
      _ ≤ Y^3*Y^(d-3) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hjR.le hjY.le _) (pow_nonneg hY.le _)
      _ = Y^d := by rw [← pow_add,show 3+(d-3)=d by omega]
  have hlocal : 0<V/(j : ℝ)^d := div_pos hV (pow_pos hjR _)
  have hsmall' : (j : ℝ)^d*(Y/(j : ℝ))^3*error α r+
      (r.den : ℝ)*(Y/(j : ℝ))^3/(V/(j : ℝ)^d)<1 := by
    have he : 0≤error α r+(r.den : ℝ)/V := by
      exact add_nonneg (error_nonneg α r) (div_nonneg (Nat.cast_nonneg _) hV.le)
    calc
      _ = ((j : ℝ)^d*(Y/(j : ℝ))^3)*(error α r+(r.den : ℝ)/V) := by field_simp
      _ ≤ Y^d*(error α r+(r.den : ℝ)/V) := mul_le_mul_of_nonneg_right hprod he
      _ = Y^d*error α r+(r.den : ℝ)*Y^d/V := by ring
      _ < 1 := hsmall
  apply scaled_match_of_short_height r s hlocal (pow_nonneg (div_nonneg hY.le hjR.le) 3)
    (show ((j^d : ℕ) : ℝ)≤(j : ℝ)^d by simp)
  · simpa only [Nat.cast_pow] using (by rw [hs]; exact hshort.le)
  · exact hsmall'

def weightedPowerSum (N d : ℕ) (V α : ℝ) : ℝ :=
  ∑j∈Finset.Icc 1 N,
    1/((j : ℝ)^2*(height (V/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))

/-- Exact weighted source bound before the final Dirichlet choice. -/
theorem weighted_power_with_approximant (N d : ℕ) (hd : 6≤d)
    {V Y α : ℝ} (hV : 0<V) (hY : 0<Y) (r : ℚ)
    (hsmall : Y^d*error α r+(r.den : ℝ)*Y^d/V<1) :
    weightedPowerSum N d V α≤(1+Real.log N)/Y+
      (2*2^(1/3 : ℝ))*(r.den.divisors.card : ℝ)/(sumCost V α r)^(2/(d : ℝ)) := by
  have hex : ∀j : ℕ,∃s : ℚ,0<j→cost (V/(j : ℝ)^d) (α*(j : ℝ)^d) s=
      height (V/(j : ℝ)^d) (α*(j : ℝ)^d) := by
    intro j
    by_cases hj : 0<j
    · obtain ⟨s,hs⟩ := exists_minimizer
        (div_pos hV (pow_pos (show (0 : ℝ)<j by exact_mod_cast hj) _)) (α*(j : ℝ)^d)
      exact ⟨s,fun _=>hs⟩
    · exact ⟨0,fun hh=>False.elim (hj hh)⟩
  choose s hs using hex
  let L := sumCost V α r
  have htL : (r.den : ℝ)≤L := by
    change (r.den : ℝ)≤(r.den : ℝ)+V*error α r
    exact le_add_of_nonneg_right (mul_nonneg hV.le (error_nonneg α r))
  have hL : 0<L := (show (0 : ℝ)<r.den by exact_mod_cast r.pos).trans_le htL
  let weight : ℕ→ℕ→ℝ := fun u j=>
    if u∣j^d then (u : ℝ)^(1/3 : ℝ)/((j : ℝ)^2*L^(1/3 : ℝ)) else 0
  have hw (u j : ℕ) : 0≤weight u j := by dsimp [weight]; split_ifs <;> positivity
  have hpoint (j : ℕ) (hj : j∈Finset.Icc 1 N) :
      1/((j : ℝ)^2*(height (V/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))≤
        1/(Y*(j : ℝ))+2^(1/3 : ℝ)*∑u∈r.den.divisors,weight u j := by
    have hjp : 0<j := (Finset.mem_Icc.mp hj).1
    have hjR : (0 : ℝ)<j := by exact_mod_cast hjp
    have hlocal : 0<V/(j : ℝ)^d := div_pos hV (pow_pos hjR _)
    by_cases hshort : height (V/(j : ℝ)^d) (α*(j : ℝ)^d)<(Y/(j : ℝ))^3
    · have hm := power_short_match (by omega : 3≤d) hjp hV hY r (s j) (hs j hjp) hshort hsmall
      have hc := scaled_denominator_class hm
      have humem : r.den/(s j).den∈r.den.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hc.1,r.den_nz⟩
      have hh := matched_height_root_le hlocal.le (by norm_num : (0 : ℝ)≤1/3) hm
        (by simpa only [Nat.cast_pow] using hs j hjp)
      have hcancel : (V/(j : ℝ)^d)*((j^d : ℕ) : ℝ)=V := by
        rw [Nat.cast_pow,div_mul_cancel₀ _ (pow_pos hjR _).ne']
      rw [hcancel,Nat.cast_pow] at hh
      have hweighted := mul_le_mul_of_nonneg_left hh (show (0 : ℝ)≤1/(j : ℝ)^2 by positivity)
      have hbound :
          1/((j : ℝ)^2*(height (V/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))≤
            2^(1/3 : ℝ)*weight (r.den/(s j).den) j := by
        dsimp [weight]
        rw [if_pos hc.2]
        convert hweighted using 1 <;> dsimp [L] <;>
          simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
      have hsingle := Finset.single_le_sum (fun u _=>hw u j) humem
      exact (hbound.trans (mul_le_mul_of_nonneg_left hsingle (by positivity))).trans
        (le_add_of_nonneg_left (by positivity))
    · have hroot : ((Y/(j : ℝ))^3)^(1/3 : ℝ)=Y/(j : ℝ) := by
        rw [← Real.rpow_natCast_mul (div_nonneg hY.le hjR.le)]
        norm_num
      have hbound :
          1/((j : ℝ)^2*(height (V/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))≤1/(Y*(j : ℝ)) := by
        have hle := Real.rpow_le_rpow (pow_nonneg (div_nonneg hY.le hjR.le) 3)
          (le_of_not_gt hshort) (by norm_num : (0 : ℝ)≤1/3)
        rw [hroot] at hle
        have hden : Y*(j : ℝ)≤(j : ℝ)^2*(height (V/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left hle (sq_nonneg (j : ℝ))
          have hid : (j : ℝ)^2*(Y/(j : ℝ))=Y*(j : ℝ) := by field_simp
          rwa [hid] at hm
        exact one_div_le_one_div_of_le (mul_pos hY hjR) hden
      exact hbound.trans (le_add_of_nonneg_right
        (mul_nonneg (by positivity) (Finset.sum_nonneg (fun u _=>hw u j))))
  have hclass (u : ℕ) (hu : u∈r.den.divisors) :
      (∑j∈Finset.Icc 1 N,weight u j)≤2/L^(2/(d : ℝ)) := by
    have huL : (u : ℝ)≤L :=
      (show (u : ℝ)≤r.den by exact_mod_cast Nat.le_of_dvd r.pos (Nat.dvd_of_mem_divisors hu)).trans htL
    simpa only [weight,← Finset.sum_filter] using
      weighted_powerClass_bound hd (Nat.pos_of_mem_divisors hu) N huL
  have hharmonic : (∑j∈Finset.Icc 1 N,1/(Y*(j : ℝ)))≤(1+Real.log N)/Y := by
    calc
      _ = (harmonic N : ℝ)/Y := by
        rw [harmonic_eq_sum_Icc,Rat.cast_sum]
        simp only [Rat.cast_inv,Rat.cast_natCast]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (harmonic_le_one_add_log N) hY.le
  calc
    _ ≤ ∑j∈Finset.Icc 1 N,(1/(Y*(j : ℝ))+2^(1/3 : ℝ)*∑u∈r.den.divisors,weight u j) :=
      Finset.sum_le_sum hpoint
    _ = (∑j∈Finset.Icc 1 N,1/(Y*(j : ℝ)))+
        2^(1/3 : ℝ)*∑u∈r.den.divisors,∑j∈Finset.Icc 1 N,weight u j := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (1+Real.log N)/Y+2^(1/3 : ℝ)*∑_u∈r.den.divisors,2/L^(2/(d : ℝ)) :=
      add_le_add hharmonic (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hclass) (by positivity))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,L]; ring

/-- The terminal weighted source bound with an actual minimizing rational.
Its intrinsic-height form is sufficient on the original auxiliary arcs. -/
theorem weighted_power_height_bound (N d : ℕ) (hd : 6≤d)
    {V Y α : ℝ} (hV : 1≤V) (hY : 0<Y) (hsize : 2*Y^d<Real.sqrt V) :
    ∃r : ℚ,cost V α r=height V α ∧ (r.den : ℝ)≤Real.sqrt V ∧
      weightedPowerSum N d V α≤(1+Real.log N)/Y+
        (2*2^(1/3 : ℝ))*(r.den.divisors.card : ℝ)/(height V α)^(2/(d : ℝ)) := by
  have hVp : 0<V := zero_lt_one.trans_le hV
  have hsqrt : 0<Real.sqrt V := Real.sqrt_pos.mpr hVp
  obtain ⟨r,hr⟩ := exists_minimizer hVp α
  have hc : cost V α r≤Real.sqrt V := hr ▸ height_le_sqrt hV α
  have hden : (r.den : ℝ)≤Real.sqrt V := (le_max_left _ _).trans hc
  have herr : error α r≤Real.sqrt V/V := by
    apply (le_div_iff₀ hVp).mpr
    simpa only [cost,error,mul_comm] using (le_max_right _ _).trans hc
  have hsmall : Y^d*error α r+(r.den : ℝ)*Y^d/V<1 := by
    have hlast : 2*Y^d*Real.sqrt V/V<1 := by
      apply (div_lt_one hVp).mpr
      have hh := mul_lt_mul_of_pos_right hsize hsqrt
      simpa only [Real.mul_self_sqrt hVp.le] using hh
    calc
      _ ≤ Y^d*(Real.sqrt V/V)+Real.sqrt V*Y^d/V := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left herr (pow_nonneg hY.le _)
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hden (pow_nonneg hY.le _)) hVp.le
      _ = 2*Y^d*Real.sqrt V/V := by ring
      _ < 1 := hlast
  have hb := weighted_power_with_approximant N d hd hVp hY r hsmall
  refine ⟨r,hr,hden,hb.trans ?_⟩
  have hcomp := (max_sum_cost_comparison hVp.le α r).1
  rw [hr] at hcomp
  apply add_le_add_left
  exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (height_pos _ _) _)
    (Real.rpow_le_rpow (height_pos _ _).le hcomp (by positivity))

#print axioms weighted_power_with_approximant
#print axioms weighted_power_height_bound
end Waring.PolicyCompletionPowerHeight
