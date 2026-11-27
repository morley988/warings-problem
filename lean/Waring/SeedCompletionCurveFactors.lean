import Waring.SeedCompletionCurveElimination

/-!
# Monic factors and coordinate-degree bounds for plane curves

A plane polynomial with a unit leading coefficient is covered by at most
its degree in the second coordinate many monic prime factors. Both coordinate-degree bounds pass to
these factors. The cover concerns literal zeros, and all bounds are uniform
in the values of the coefficients.
-/

noncomputable section
open scoped BigOperators Polynomial Polynomial.Bivariate
open Polynomial UniqueFactorizationMonoid
namespace Waring.SeedCompletionCurveFactors

variable {K : Type*} [Field K]

/-- Swapping the variables transposes the two coefficient indices. -/
theorem coeff_coeff_swap (p : K[X][Y]) (i j : ℕ) :
    ((Polynomial.Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add,coeff_add] using congrArg₂ (·+·) hp hq
  | monomial n a =>
      induction a using Polynomial.induction_on' with
      | add a b ha hb =>
          simpa only [map_add,coeff_add,monomial_add] using congrArg₂ (·+·) ha hb
      | monomial m r =>
          rw [Polynomial.Bivariate.swap_monomial_monomial]
          simp only [coeff_monomial]
          split_ifs <;> simp_all [coeff_monomial]

/-- Bounding the first coordinate degree bounds every coefficient polynomial.
This applies even when a coefficient or the whole polynomial is zero. -/
theorem coefficient_natDegree_le_swap (p : K[X][Y]) (n : ℕ) :
    (p.coeff n).natDegree ≤ (Polynomial.Bivariate.swap p).natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [← coeff_coeff_swap p i n,coeff_eq_zero_of_natDegree_lt hi,coeff_zero]

/-- Coordinate degrees cannot increase on passing to a divisor. -/
theorem factor_coefficient_natDegree_le {p F : K[X][Y]} (hF : F ≠ 0)
    (hp : p ∣ F) (n : ℕ) :
    (p.coeff n).natDegree ≤ (Polynomial.Bivariate.swap F).natDegree := by
  apply (coefficient_natDegree_le_swap p n).trans
  apply natDegree_le_of_dvd (map_dvd (Polynomial.Bivariate.swap.toRingHom) hp)
  exact (map_ne_zero_iff (Polynomial.Bivariate.swap.toRingHom)
    (Polynomial.Bivariate.swap.injective)).mpr hF

/-- The distinct normalized prime factors of the literal plane polynomial. -/
def curveFactors (F : K[X][Y]) : Finset (K[X][Y]) := by
  classical
  exact (normalizedFactors F).toFinset

theorem curveFactor_prime {F p : K[X][Y]} (hp : p ∈ curveFactors F) : Prime p := by
  classical
  exact prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)

theorem curveFactor_dvd {F p : K[X][Y]} (hp : p ∈ curveFactors F) : p ∣ F := by
  classical
  exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)

theorem curveFactor_monic {F p : K[X][Y]} (hF : IsUnit F.leadingCoeff) (hp : p ∈ curveFactors F) :
    p.Monic := by
  classical
  have hnorm : normalize p=p := normalize_normalized_factor p (Multiset.mem_toFinset.mp hp)
  have hunit : IsUnit p.leadingCoeff := isUnit_of_dvd_unit
    (leadingCoeff_dvd_leadingCoeff (curveFactor_dvd hp)) hF
  rw [← hnorm,Monic,leadingCoeff_normalize]
  exact normalize_eq_one.mpr hunit

theorem curveFactor_natDegree_pos {F p : K[X][Y]}
    (hF : IsUnit F.leadingCoeff) (hp : p ∈ curveFactors F) : 0 < p.natDegree := by
  have hmon := curveFactor_monic hF hp
  apply Nat.pos_of_ne_zero
  intro hz
  have hone := hmon.natDegree_eq_zero_iff_eq_one.mp hz
  exact (curveFactor_prime hp).not_unit (hone ▸ isUnit_one)

/-- The number of distinct prime components is at most the degree. -/
theorem curveFactors_card_le {F : K[X][Y]} (hF : IsUnit F.leadingCoeff) :
    (curveFactors F).card ≤ F.natDegree := by
  classical
  have hsum (s : Multiset (K[X][Y]))
      (hs : ∀ p ∈ s, 1 ≤ p.natDegree) : s.card ≤ (s.map natDegree).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons p s ih =>
        have hp := hs p (Multiset.mem_cons_self _ _)
        have hh := ih (fun q hq => hs q (Multiset.mem_cons_of_mem hq))
        simpa only [Multiset.card_cons,Multiset.map_cons,Multiset.sum_cons] using
          (show s.card+1 ≤ p.natDegree+(s.map natDegree).sum by omega)
  have hdeg : ((normalizedFactors F).map natDegree).sum=F.natDegree := by
    rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated
      (prod_normalizedFactors (leadingCoeff_ne_zero.mp hF.ne_zero)))
  calc
    (curveFactors F).card ≤ (normalizedFactors F).card := Multiset.toFinset_card_le _
    _ ≤ ((normalizedFactors F).map natDegree).sum := hsum _ (fun p hp =>
      curveFactor_natDegree_pos hF (Multiset.mem_toFinset.mpr hp))
    _ = _ := hdeg

/-- Every actual zero lies on one of the displayed monic prime components. -/
theorem exists_curveFactor_zero {F : K[X][Y]} (hF : IsUnit F.leadingCoeff) (x y : K)
    (hzero : F.evalEval x y=0) :
    ∃ p ∈ curveFactors F, p.evalEval x y=0 := by
  classical
  have hprod := congrArg (Polynomial.evalEval x y)
    (prod_normalizedFactors_eq (leadingCoeff_ne_zero.mp hF.ne_zero))
  rw [evalEval_multiset_prod,normalize_apply,evalEval_mul,hzero,zero_mul] at hprod
  obtain ⟨p,hp,hpz⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
  exact ⟨p,Multiset.mem_toFinset.mpr hp,hpz⟩

#print axioms factor_coefficient_natDegree_le
#print axioms curveFactors_card_le
#print axioms exists_curveFactor_zero
end Waring.SeedCompletionCurveFactors
