import Waring.SeedCompletionTerminalIdentityCoefficients
import Waring.SeedCompletionTerminalIdentityCumulants
import Waring.PolicyCompletionMajorFamily

/-! # Actual source polynomial equality forces the weighted sparse equations -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalIdentity
open IntegerDifferencePolynomial PolicyCompletionMajorFamily

def naturalRational {j : ℕ} (h m : Fin j → ℕ) : List (ℚ×ℚ) :=
  List.ofFn (fun i => ((h i : ℚ),(m i : ℚ)))

theorem rationalParameters_natural {j : ℕ} (h m : Fin j → ℕ) :
    rationalParameters (naturalParameters h m)=naturalRational h m := by
  simp [rationalParameters,naturalParameters,naturalRational,List.map_ofFn]
  funext i
  simp only [Function.comp_apply,Int.cast_natCast]

theorem naturalRational_nonzero {j : ℕ} (h m : Fin j → ℕ) (hm : ∀ i,0<m i) :
    ∀ p∈naturalRational h m,p.2≠0 := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact Nat.cast_ne_zero.mpr (hm i).ne'

theorem naturalParameters_nonzero {j : ℕ} (h m : Fin j → ℕ) (hm : ∀ i,0<m i) :
    ∀ p∈naturalParameters h m,p.2≠0 := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact Nat.cast_ne_zero.mpr (hm i).ne'

theorem naturalRational_factor {j : ℕ} (h m : Fin j → ℕ) :
    symbolFactor (naturalRational h m)=(2 : ℚ)^j*∏ i,(h i : ℚ) := by
  simp only [symbolFactor,naturalRational,List.length_ofFn,List.map_ofFn,Fin.prod_ofFn,
    Function.comp_apply]

theorem naturalRational_factor_ne_zero {j : ℕ} (h m : Fin j → ℕ) (hh : ∀ i,0<h i) :
    symbolFactor (naturalRational h m)≠0 := by
  rw [naturalRational_factor]
  apply mul_ne_zero (by positivity)
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.cast_ne_zero.mpr (hh i).ne')

theorem natural_power_sums_of_polynomial_eq {j : ℕ} (k : ℕ)
    (h m n : Fin j → ℕ) (hh : ∀ i,0<h i) (hm : ∀ i,0<m i) (hn : ∀ i,0<n i)
    (heq : powerPolynomial k (naturalParameters h m)=
      powerPolynomial k (naturalParameters h n)) {r : ℕ}
    (hr : 1≤r) (hr8 : r≤8) (hkr : j+2*r≤k) :
    (∑ i,(h i : ℤ)^(2*r)*(m i : ℤ)^(2*k*r))=
      ∑ i,(h i : ℤ)^(2*r)*(n i : ℤ)^(2*k*r) := by
  have hp : rationalPower k (naturalRational h m) k=
      rationalPower k (naturalRational h n) k := by
    rw [← rationalParameters_natural,← rationalParameters_natural,
      rationalPower_eq_integer k _ (naturalParameters_nonzero h m hm),
      rationalPower_eq_integer k _ (naturalParameters_nonzero h n hn),heq]
  have hf : symbolFactor (naturalRational h m)=symbolFactor (naturalRational h n) := by
    rw [naturalRational_factor,naturalRational_factor]
  have ha : SeriesAgree (2*r) (unitSymbol k (naturalRational h m))
      (unitSymbol k (naturalRational h n)) := by
    intro t ht
    exact unitSymbol_coeff_eq_of_power_eq k _ _ (naturalRational_nonzero h m hm)
      (naturalRational_nonzero h n hn) (by simp [naturalRational]) hf
      (naturalRational_factor_ne_zero h m hh) hp t
      (by simp only [naturalRational,List.length_ofFn]; omega)
  have H := powers_eq_of_unitSymbol_agree k _ _ hr hr8 ha
  simp only [naturalRational,List.map_ofFn,Fin.sum_ofFn,Function.comp_apply,
    mul_pow,← pow_mul] at H
  have hexp : k*(2*r)=2*k*r := by ring
  rw [hexp] at H
  exact_mod_cast H

#print axioms natural_power_sums_of_polynomial_eq
end Waring.SeedCompletionTerminalIdentity
