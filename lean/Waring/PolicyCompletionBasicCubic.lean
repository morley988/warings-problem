import Waring.CubicRootSampling
import Waring.CoefficientPower

/-!
# The initial cubic resummation in the basic coefficient estimate

This proves the first analytic step of Vaughan--Wooley (1995), Lemma4.3.
Short geometric sums force their nearest-integer fractions to agree with
a single rational approximant before the cubic divisibility classes are
summed.  Keeping local denominator one gives the source cutoff J/H^3,
rather than the square-root cutoff from general coefficient sampling.
-/

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Waring.PolicyCompletionBasicCubic
open RationalHeight CubicExceptionalSampling CubicDivisorClasses
open QuadraticModulation CoefficientPower

theorem linearSumBound_le_smooth_kernel (J : ℕ) (β : ℝ) :
    linearSumBound J β≤2*(J : ℝ)/(1+(J : ℝ)*integerDistance β) := by
  have hd : 0 ≤ integerDistance β := abs_nonneg _
  have hden : 0<1+(J : ℝ)*integerDistance β := by positivity
  by_cases hz : integerDistance β=0
  · simp only [linearSumBound,hz,ite_true,mul_zero,add_zero,div_one]
    have := Nat.cast_nonneg (α := ℝ) J
    linarith
  · have hdp : 0 < integerDistance β := lt_of_le_of_ne hd (Ne.symm hz)
    have hlen : min (J : ℝ) (1/(2*integerDistance β))≤J := min_le_left _ _
    have hrec : min (J : ℝ) (1/(2*integerDistance β))*integerDistance β≤1/2 := by
      have hh := mul_le_mul_of_nonneg_right
        (min_le_right (J : ℝ) (1/(2*integerDistance β))) hd
      have heq : 1/(2*integerDistance β)*integerDistance β=1/2 := by field_simp
      rwa [heq] at hh
    rw [linearSumBound,if_neg hz]
    apply (le_div_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hrec (show (0 : ℝ)≤J by positivity)
    nlinarith

def nearestFraction (β : ℝ) : ℚ := (round β : ℤ)

@[simp] theorem nearestFraction_sumCost (J β : ℝ) :
    sumCost J β (nearestFraction β)=1+J*integerDistance β := by
  simp only [nearestFraction,sumCost,error,Rat.den_intCast,Rat.num_intCast,
    Nat.cast_one,one_mul,integerDistance]

/-- The local denominator is exactly one. This is the sharper rigidity
condition specific to the second coefficient moment. -/
theorem geometric_cross_match {J Y β : ℝ} {H h : ℕ} (r : ℚ)
    (hJ : 0<J) (hY : 0<Y) (hhH : h≤H)
    (hnear : integerDistance (β*(h : ℝ)^3)<Y/J)
    (hsmall : (H : ℝ)^3*error β r+(r.den : ℝ)*Y/J<1) :
    CrossMatch r (nearestFraction (β*(h : ℝ)^3)) h := by
  have ht : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have hhR : (h : ℝ)^3≤(H : ℝ)^3 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hhH) _
  have herr : (h : ℝ)^3*error β r+(r.den : ℝ)*integerDistance (β*(h : ℝ)^3)<1 := by
    have he := mul_le_mul_of_nonneg_right hhR (error_nonneg β r)
    have hn := mul_lt_mul_of_pos_left hnear ht
    rw [← mul_div_assoc] at hn
    linarith
  have hh := SamplingArithmetic.exceptional_rigidity
    (a := r.num) (c := round (β*(h : ℝ)^3)) (h := (h : ℤ))
    (s := 1) (t := (r.den : ℤ)) (α := β) (by
      simpa only [Int.cast_one,Int.cast_natCast,mul_one,
        abs_of_nonneg (show (0 : ℝ)≤(h : ℝ)^3 by positivity),abs_of_pos ht,
        integerDistance,error] using herr)
  simpa only [CrossMatch,nearestFraction,Rat.den_intCast,Rat.num_intCast,
    Nat.cast_one,mul_one] using hh

/-- A finite geometric sum over the cubes, with the actual rational error
and divisor count retained. There is no unproved analytic input. -/
theorem cubic_geometric_with_approximant (H J : ℕ) (r : ℚ) {Y β : ℝ}
    (hH : 0<H) (hJ : 0<J) (hY : 0<Y)
    (hsmall : (H : ℝ)^3*error β r+(r.den : ℝ)*Y/(J : ℝ)<1) :
    (∑h∈Finset.Icc 1 H,linearSumBound J (β*(h : ℝ)^3))≤
      (J : ℝ)*H/Y+2*(J : ℝ)*(r.den.divisors.card : ℝ)*
        ((H : ℝ)/(sumCost ((H : ℝ)^3*J) β r)^(1/3 : ℝ))*(1+Real.log H) := by
  have hJR : (0 : ℝ)<J := by exact_mod_cast hJ
  let S : Finset ℕ := (Finset.Icc 1 H).filter fun h : ℕ => integerDistance (β*(h : ℝ)^3)<Y/(J : ℝ)
  let s : ℕ→ℚ := fun h => nearestFraction (β*(h : ℝ)^3)
  have hmatch : ∀h∈S,CrossMatch r (s h) h := by
    intro h hh
    obtain ⟨hh,hnear⟩ := Finset.mem_filter.mp hh
    exact geometric_cross_match r hJR hY (Finset.mem_Icc.mp hh).2 hnear hsmall
  have hex := exceptional_reciprocal_cube_root_sum S H r s (α := β) hH hJR.le
    (Finset.filter_subset _ _) hmatch
  have hpoint (h : ℕ) :
      linearSumBound J (β*(h : ℝ)^3)≤
        (if integerDistance (β*(h : ℝ)^3)<Y/(J : ℝ) then
          2*(J : ℝ)*(1/sumCost J (β*(h : ℝ)^3) (s h)) else 0)+(J : ℝ)/Y := by
    by_cases hn : integerDistance (β*(h : ℝ)^3)<Y/(J : ℝ)
    · rw [if_pos hn]
      have hb := linearSumBound_le_smooth_kernel J (β*(h : ℝ)^3)
      rw [← nearestFraction_sumCost] at hb
      apply hb.trans
      dsimp [s]
      rw [mul_one_div]
      exact le_add_of_nonneg_right (div_nonneg hJR.le hY.le)
    · rw [if_neg hn,zero_add]
      have hd : Y/(J : ℝ) ≤ integerDistance (β*(h : ℝ)^3) := le_of_not_gt hn
      have hdp : 0 < integerDistance (β*(h : ℝ)^3) := (div_pos hY hJR).trans_le hd
      rw [linearSumBound,if_neg hdp.ne']
      apply (min_le_right _ _).trans
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hdp) hY).mpr
      have hh := (div_le_iff₀ hJR).mp hd
      nlinarith [mul_nonneg hJR.le hdp.le]
  calc
    _ ≤ ∑h∈Finset.Icc 1 H,
        ((if integerDistance (β*(h : ℝ)^3)<Y/(J : ℝ) then
          2*(J : ℝ)*(1/sumCost J (β*(h : ℝ)^3) (s h)) else 0)+(J : ℝ)/Y) :=
      Finset.sum_le_sum (fun h _ => hpoint h)
    _ = 2*(J : ℝ)*(∑h∈S,1/sumCost J (β*(h : ℝ)^3) (s h))+(J : ℝ)*H/Y := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.mul_sum]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.sub_add_cancel (by omega : 1≤H+1),
        Nat.cast_id]
      simp [S]
      ring
    _ ≤ 2*(J : ℝ)*((r.den.divisors.card : ℝ)*
        ((H : ℝ)/(sumCost ((H : ℝ)^3*J) β r)^(1/3 : ℝ))*(1+Real.log H))+
        (J : ℝ)*H/Y := add_le_add_right (mul_le_mul_of_nonneg_left hex (by positivity)) _
    _ = _ := by ring

/-- Dirichlet supplies the approximant at the source's J/H^3 cutoff.
The factor sixteen secures strict integer separation and is absorbed by
the fixed constants in the final basic resource. -/
theorem cubic_geometric_bound (H J : ℕ) {Y : ℝ}
    (hH : 0<H) (hJ : 0<J) (hY : 0<Y)
    (hsize : 16*(H : ℝ)^3*Y≤(J : ℝ)) (β : ℝ) :
    ∃r : ℚ,
      cost (((H : ℝ)^3*J)/Y) β r=height (((H : ℝ)^3*J)/Y) β ∧
      (r.den : ℝ)≤Real.sqrt (((H : ℝ)^3*J)/Y) ∧
      (∑h∈Finset.Icc 1 H,linearSumBound J (β*(h : ℝ)^3))≤
        (J : ℝ)*H/Y+2*(J : ℝ)*(r.den.divisors.card : ℝ)*
          ((H : ℝ)/(height ((H : ℝ)^3*J) β)^(1/3 : ℝ))*(1+Real.log H) := by
  have hHR : (1 : ℝ)≤H := by exact_mod_cast hH
  have hJR : (0 : ℝ)<J := by exact_mod_cast hJ
  have hH3 : (1 : ℝ)≤(H : ℝ)^3 := one_le_pow₀ hHR
  have hJY : Y≤(J : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hH3 hY.le]
  have hVY : Y≤(H : ℝ)^3*J := hJY.trans
    (le_mul_of_one_le_left hJR.le hH3)
  let W : ℝ := ((H : ℝ)^3*J)/Y
  have hW : 1≤W := (one_le_div hY).mpr hVY
  have hWp : 0<W := zero_lt_one.trans_le hW
  let R := Real.sqrt W
  have hR : 0≤R := Real.sqrt_nonneg _
  have hR2 : R^2=W := Real.sq_sqrt hWp.le
  obtain ⟨r,hr⟩ := exists_minimizer hWp β
  have hc : cost W β r≤R := hr ▸ height_le_sqrt hW β
  have hd : (r.den : ℝ)≤R := (le_max_left _ _).trans hc
  have he : error β r≤R/W := by
    apply (le_div_iff₀ hWp).mpr
    simpa only [cost,error,mul_comm] using (le_max_right _ _).trans hc
  have hRrel : R^2*Y=(H : ℝ)^3*J := by
    rw [hR2]
    exact div_mul_cancel₀ _ hY.ne'
  have hRy : 16*(R*Y)^2≤(J : ℝ)^2 := by
    have hm := mul_le_mul_of_nonneg_right hsize hJR.le
    have hid : (R*Y)^2=((H : ℝ)^3*J)*Y := by
      calc
        _ = (R^2*Y)*Y := by ring
        _ = _ := by rw [hRrel]
    rw [hid]
    nlinarith only [hm]
  have hRy' : 2*(R*Y)<(J : ℝ) := by
    nlinarith only [hRy,hJR,sq_nonneg ((J : ℝ)-2*(R*Y))]
  have hsmall : (H : ℝ)^3*error β r+(r.den : ℝ)*Y/(J : ℝ)<1 := by
    have hfirst := mul_le_mul_of_nonneg_left he (pow_nonneg (by positivity : (0 : ℝ)≤H) 3)
    have hid : (H : ℝ)^3*(R/W)=R*Y/(J : ℝ) := by
      dsimp [W]
      field_simp
    rw [hid] at hfirst
    have hsecond : (r.den : ℝ)*Y/(J : ℝ)≤R*Y/(J : ℝ) := by gcongr
    have hlast : 2*(R*Y)/(J : ℝ)<1 := (div_lt_one hJR).mpr hRy'
    calc
      _ ≤ R*Y/(J : ℝ)+R*Y/(J : ℝ) := add_le_add hfirst hsecond
      _ = 2*(R*Y)/(J : ℝ) := by ring
      _ < 1 := hlast
  have hb := cubic_geometric_with_approximant H J r hH hJ hY hsmall
  refine ⟨r,hr,hd,hb.trans ?_⟩
  have hV : 0≤(H : ℝ)^3*J := by positivity
  have hcompare : height ((H : ℝ)^3*J) β≤sumCost ((H : ℝ)^3*J) β r :=
    (height_le_cost _ _ _).trans (max_sum_cost_comparison hV β r).1
  have hlog : 0≤1+Real.log (H : ℝ) := by
    have := Real.log_nonneg hHR
    linarith
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ hlog
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (height_pos _ _) _)
  exact Real.rpow_le_rpow (height_pos _ _).le hcompare (by norm_num)

#print axioms cubic_geometric_with_approximant
#print axioms cubic_geometric_bound
end Waring.PolicyCompletionBasicCubic
