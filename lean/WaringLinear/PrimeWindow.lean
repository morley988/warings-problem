import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Prime reciprocal mass on a power interval -/
noncomputable section
namespace WaringLinear.PrimeWindow
open MeasureTheory Finset Set
open scoped BigOperators Interval

def flag (n : ℕ) : ℝ := if n.Prime then 1 else 0

def count (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

def mass (x y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (p:ℝ)⁻¹

theorem cumulative (n : ℕ) : ∑ p∈Finset.Icc 0 n, flag p=(Nat.primeCounting n:ℝ) := by
  rw [←Nat.range_succ_eq_Icc_zero,Nat.primeCounting,←Nat.primesBelow_card_eq_primeCounting']
  simp [flag,Nat.primesBelow]

private theorem deriv_reciprocal {x : ℝ} (hx : x≠0) :
    deriv (fun t : ℝ => t⁻¹) x= -(1/x^2) := by
  simpa [one_div] using (hasDerivAt_inv hx).deriv

/-- Stieltjes summation in terms of the actual prime-counting function.
The endpoints use the half-open prime interval (x,y]. -/
theorem abel {x y : ℝ} (hx : 0<x) (hy : x≤y) :
    mass x y=count y/y-count x/x+∫ t in x..y, count t/t^2 := by
  have hrec : ContinuousOn (fun t : ℝ => -(1/t^2)) (Set.Icc x y) :=
    (continuousOn_const.div (continuous_id.pow 2).continuousOn
      (fun t ht => pow_ne_zero _ (hx.trans_le ht.1).ne')).neg
  have hder : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc x y) :=
    hrec.integrableOn_Icc.congr_fun (fun t ht => (deriv_reciprocal (hx.trans_le ht.1).ne').symm)
      measurableSet_Icc
  have H := sum_mul_eq_sub_sub_integral_mul flag hx.le hy
    (fun t ht => (hasDerivAt_inv (hx.trans_le ht.1).ne').differentiableAt) hder
  have hs : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, (n:ℝ)⁻¹*flag n)=mass x y := by
    simp [mass,flag,Finset.sum_filter,mul_ite]
  rw [hs] at H
  simp only [cumulative] at H
  have he : (∫ t in Set.Ioc x y, deriv (fun t : ℝ => t⁻¹) t*(Nat.primeCounting ⌊t⌋₊:ℝ)) =
      -(∫ t in x..y,count t/t^2) := by
    rw [intervalIntegral.integral_of_le hy,←integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [deriv_reciprocal (hx.trans ht.1).ne']
    unfold count
    ring
  rw [he,sub_neg_eq_add] at H
  simpa only [count,div_eq_inv_mul] using H

theorem count_integrable {x y : ℝ} (hx : 0<x) (hy : x≤y) :
    IntegrableOn (fun t : ℝ => count t/t^2) (Set.Ioc x y) := by
  have hc : ContinuousOn (fun t : ℝ => 1/t^2) (Set.Ici x) :=
    continuousOn_const.div (continuous_id.pow 2).continuousOn
      (fun t ht => pow_ne_zero _ (hx.trans_le ht).ne')
  have H := locallyIntegrableOn_mul_sum_Icc flag (m:=0) hx.le
    (hc.locallyIntegrableOn measurableSet_Ici)
  have H₁ := H.integrableOn_compact_subset (t:=Set.Icc x y) (fun t ht => ht.1) isCompact_Icc
  have A := H₁.mono_set Set.Ioc_subset_Icc_self
  apply A.congr_fun _ measurableSet_Ioc
  intro t _
  dsimp only
  rw [cumulative]
  unfold count
  ring

theorem reciprocal_log_continuous {x y : ℝ} (hx : 1<x) :
    ContinuousOn (fun t : ℝ => 1/(t*Real.log t)) (Set.Icc x y) := by
  have hlog : ContinuousOn Real.log (Set.Icc x y) := Real.continuousOn_log.mono
    (fun t ht => (zero_lt_one.trans (hx.trans_le ht.1)).ne')
  exact continuousOn_const.div (continuous_id.continuousOn.mul hlog)
    (fun t ht => mul_ne_zero (zero_lt_one.trans (hx.trans_le ht.1)).ne'
      (Real.log_pos (hx.trans_le ht.1)).ne')

theorem kernel_integral {x y : ℝ} (hx : 1<x) (hy : x≤y) :
    (∫ t in x..y, 1/(t*Real.log t)) = Real.log (Real.log y)-Real.log (Real.log x) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t : ℝ => Real.log (Real.log t))
  · intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht' : 1<t := hx.trans_le ht.1
    have hd := (Real.hasDerivAt_log (Real.log_pos ht').ne').comp t
      (Real.hasDerivAt_log (zero_lt_one.trans ht').ne')
    simpa [one_div,mul_inv_rev,Function.comp_def] using hd
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hy]
    exact reciprocal_log_continuous hx

#print axioms abel
end WaringLinear.PrimeWindow
