import Waring.SeedCompletionTerminalIdentitySinh

/-! # Recovering the normalized symbol from the actual source polynomial -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalIdentity
open Polynomial IntegerDifferencePolynomial

def rationalParameters (params : List (ℤ×ℤ)) : List (ℚ×ℚ) :=
  params.map (fun hm => ((hm.1 : ℚ),(hm.2 : ℚ)))

theorem integer_difference_map (k : ℕ) (h m : ℤ) (hm : m≠0) (f : Polynomial ℤ) :
    (difference k h m f).map (Int.castRingHom ℚ)=
      rationalDifference k (h : ℚ) (m : ℚ) (f.map (Int.castRingHom ℚ)) := by
  have hmp : (m : ℚ)^k≠0 := pow_ne_zero k (by exact_mod_cast hm)
  have H0 := congrArg (Polynomial.map (Int.castRingHom ℚ)) (difference_mul k h m f)
  have H : Polynomial.C ((m : ℚ)^k)*(difference k h m f).map (Int.castRingHom ℚ)=
      (f.map (Int.castRingHom ℚ)).comp (Polynomial.X+Polynomial.C ((h : ℚ)*(m : ℚ)^k))-
      (f.map (Int.castRingHom ℚ)).comp (Polynomial.X-Polynomial.C ((h : ℚ)*(m : ℚ)^k)) := by
    simpa only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_sub,Polynomial.map_comp,
      Polynomial.map_add,Polynomial.map_X,Polynomial.map_pow,map_mul,map_pow] using H0
  unfold rationalDifference translate
  simp only [Polynomial.coe_compRingHom_apply]
  rw [show Polynomial.X+Polynomial.C (-((h : ℚ)*(m : ℚ)^k))=
    Polynomial.X-Polynomial.C ((h : ℚ)*(m : ℚ)^k) by rw [map_neg]; ring]
  rw [← H,← mul_assoc,← map_mul,inv_mul_cancel₀ hmp,map_one,one_mul]

theorem rationalPower_eq_integer (k : ℕ) (params : List (ℤ×ℤ))
    (hm : ∀ p∈params,p.2≠0) :
    rationalPower k (rationalParameters params) k=
      (powerPolynomial k params).map (Int.castRingHom ℚ) := by
  induction params with
  | nil => simp [rationalParameters,rationalPower,powerPolynomial]
  | cons p rest ih =>
      have hr := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))
      unfold rationalParameters at hr
      simp only [rationalParameters,List.map_cons,rationalPower,powerPolynomial]
      rw [hr]
      exact (integer_difference_map k p.1 p.2 (hm p (List.mem_cons_self ..)) _).symm

theorem exponential_product_coeff (f : PowerSeries ℚ) (d r : ℕ) :
    (PowerSeries.coeff (d+r)
      (polyExp Polynomial.X*PowerSeries.map Polynomial.C f)).coeff d=
      PowerSeries.coeff r f/(d.factorial : ℚ) := by
  rw [PowerSeries.coeff_mul,Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single (d,r)]
  · simp only [PowerSeries.coeff_map,polyExp,PowerSeries.coeff_rescale,PowerSeries.coeff_exp]
    change (Polynomial.X^d*Polynomial.C (1/(d.factorial : ℚ))*
      Polynomial.C (PowerSeries.coeff r f)).coeff d=_
    rw [Polynomial.coeff_mul_C,Polynomial.coeff_mul_C,Polynomial.coeff_X_pow_self]
    ring
  · intro ij hij hne
    have hi : ij.1≠d := by
      intro hid
      have hs := Finset.mem_antidiagonal.mp hij
      have hr : ij.2=r := by omega
      exact hne (Prod.ext hid hr)
    simp only [PowerSeries.coeff_map,polyExp,PowerSeries.coeff_rescale,PowerSeries.coeff_exp]
    change (Polynomial.X^ij.1*Polynomial.C (1/(ij.1.factorial : ℚ))*
      Polynomial.C (PowerSeries.coeff ij.2 f)).coeff d=0
    rw [Polynomial.coeff_mul_C,Polynomial.coeff_mul_C,Polynomial.coeff_X_pow,
      if_neg (Ne.symm hi)]
    ring
  · intro hbad
    exact False.elim (hbad (Finset.mem_antidiagonal.mpr rfl))

theorem sourceSeries_coefficient_symbol (k : ℕ) (params : List (ℚ×ℚ))
    (hm : ∀ p∈params,p.2≠0) (r : ℕ) (hr : params.length+r≤k) :
    (PowerSeries.coeff k (sourceSeries k params)).coeff (k-params.length-r)=
      symbolFactor params*PowerSeries.coeff r (unitSymbol k params)/
        ((k-params.length-r).factorial : ℚ) := by
  have hk : k=(k-params.length-r)+(r+params.length) := by omega
  unfold sourceSeries
  have H := exponential_product_coeff (rawSymbol k params) (k-params.length-r) (r+params.length)
  rw [← hk] at H
  rw [H]
  rw [rawSymbol_eq_unitSymbol k params hm,PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul]

theorem unitSymbol_coeff_eq_of_power_eq (k : ℕ) (params other : List (ℚ×ℚ))
    (hm : ∀ p∈params,p.2≠0) (hn : ∀ p∈other,p.2≠0)
    (hlen : params.length=other.length) (hfac : symbolFactor params=symbolFactor other)
    (hfac0 : symbolFactor params≠0)
    (hpoly : rationalPower k params k=rationalPower k other k)
    (r : ℕ) (hr : params.length+r≤k) :
    PowerSeries.coeff r (unitSymbol k params)=PowerSeries.coeff r (unitSymbol k other) := by
  have hs : PowerSeries.coeff k (sourceSeries k params)=
      PowerSeries.coeff k (sourceSeries k other) := by
    rw [sourceSeries_coeff,sourceSeries_coeff,hpoly]
  have hc := congrArg (fun f : Polynomial ℚ => f.coeff (k-params.length-r)) hs
  dsimp only at hc
  rw [sourceSeries_coefficient_symbol k params hm r hr] at hc
  have hro : other.length+r≤k := by omega
  rw [hlen,sourceSeries_coefficient_symbol k other hn r hro,← hfac] at hc
  have hfact : ((k-other.length-r).factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero _
  exact mul_left_cancel₀ hfac0 ((div_left_inj' hfact).mp hc)

#print axioms rationalPower_eq_integer
#print axioms unitSymbol_coeff_eq_of_power_eq
end Waring.SeedCompletionTerminalIdentity
