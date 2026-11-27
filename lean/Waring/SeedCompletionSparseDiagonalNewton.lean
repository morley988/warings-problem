import Waring.FiniteFieldMordellNewton

/-!
# Newton's invariant for the progression of sparse degrees

Equal signed power sums of J positive coordinates minus one coordinate
determine the product of the J signed differences. This specialization of
the symmetric diagonal counting argument uses only Newton's identities.
The later divisor count applies it to the powers x^(2k).
-/

noncomputable section
open scoped BigOperators Polynomial
namespace Waring.SeedCompletionSparseDiagonal
open FiniteFieldMordell

section Field
variable {K : Type*} [Field K] {d m : ℕ}

theorem esymm_eq_of_initial_power_sums {x y : Fin d → K}
    (hchar : ∀j : ℕ,1≤j→j≤m→(j : K)≠0)
    (hpower : ∀j : ℕ,1≤j→j≤m→(∑i,(x i)^j)=∑i,(y i)^j)
    (j : ℕ) (hj : j≤m) : esymmValue x j=esymmValue y j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj0 : j=0
    · subst j
      simp [esymmValue,MvPolynomial.esymm_zero]
    apply mul_left_cancel₀ (hchar j (by omega) hj)
    rw [newton_value,newton_value]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨hanti,halt⟩ := Finset.mem_filter.mp ha
    have heq := Finset.mem_antidiagonal.mp hanti
    rw [ih a.1 halt (by omega),hpower a.2 (by omega) (by omega)]

theorem rootPolynomial_eval_expansion (x : Fin d → K) (t : K) :
    (rootPolynomial x).eval t=
      ∑j∈Finset.range (d+1),(-1 : K)^j*esymmValue x j*t^(d-j) := by
  let s := Finset.univ.val.map x
  have hx : rootPolynomial x=(s.map (fun z => Polynomial.X-Polynomial.C z)).prod := by
    simp only [rootPolynomial,s,Multiset.map_map,Finset.prod]
    rfl
  have hs : s.card=d := by simp [s]
  rw [hx,Multiset.prod_X_sub_X_eq_sum_esymm,hs,Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : s.esymm j=esymmValue x j :=
    (MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin d) K j x).symm
  rw [he]
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_neg,
    Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_X]
  ring

theorem rootPolynomial_difference_constant {x y : Fin (d+1) → K}
    (hchar : ∀j : ℕ,1≤j→j≤d→(j : K)≠0)
    (hpower : ∀j : ℕ,1≤j→j≤d→(∑i,(x i)^j)=∑i,(y i)^j)
    (t : K) :
    (rootPolynomial x).eval t-(rootPolynomial y).eval t=
      (-1 : K)^(d+1)*(esymmValue x (d+1)-esymmValue y (d+1)) := by
  rw [rootPolynomial_eval_expansion,rootPolynomial_eval_expansion,← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (d+1)]
  · simp only [Nat.sub_self,pow_zero,mul_one]
    ring
  · intro j hj hne
    have hjd : j≤d := by have := Finset.mem_range.mp hj; omega
    rw [esymm_eq_of_initial_power_sums hchar hpower j hjd,sub_self]
  · intro hbad
    exact False.elim (hbad (Finset.mem_range.mpr (by omega)))

def signedPower {J : ℕ} (x : Fin (J+1) → K) (r : ℕ) : K :=
  (∑i : Fin J,(x i.succ)^r)-(x 0)^r

def signedProduct {J : ℕ} (x : Fin (J+1) → K) : K :=
  ∏i : Fin J,(x 0-x i.succ)

theorem signedProduct_eq_of_signed_powers {J : ℕ} {x y : Fin (J+1) → K}
    (hchar : ∀ r : ℕ, 1 ≤ r → r ≤ J → (r : K) ≠ 0)
    (hs : ∀ r : ℕ, 1 ≤ r → r ≤ J → signedPower x r=signedPower y r) :
    signedProduct x=signedProduct y := by
  by_cases hc : x 0=y 0
  · have hp : ∀ r : ℕ, 1 ≤ r → r ≤ J →
        (∑i : Fin J,(x i.succ)^r)=∑i : Fin J,(y i.succ)^r := by
      intro r hr hrJ
      have hh := hs r hr hrJ
      unfold signedPower at hh
      rw [hc] at hh
      exact sub_left_injective hh
    have he := rootPolynomial_eq_of_power_sums hchar hp
    have hv := congrArg (fun p : K[X] => p.eval (x 0)) he
    simpa only [signedProduct,rootPolynomial,Polynomial.eval_prod,
      Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,hc] using hv
  · let u : Fin (J+1) → K := Fin.cons (y 0) (fun i : Fin J => x i.succ)
    let v : Fin (J+1) → K := Fin.cons (x 0) (fun i : Fin J => y i.succ)
    have hp : ∀ r : ℕ, 1 ≤ r → r ≤ J → (∑i,(u i)^r)=∑i,(v i)^r := by
      intro r hr hrJ
      have hh := hs r hr hrJ
      unfold signedPower at hh
      simp only [u,v,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      linear_combination hh
    have he := (rootPolynomial_difference_constant hchar hp (x 0)).trans
      (rootPolynomial_difference_constant hchar hp (y 0)).symm
    have hprod : (x 0-y 0)*signedProduct x=(x 0-y 0)*signedProduct y := by
      simp only [rootPolynomial,Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_sub,
        Polynomial.eval_X,Polynomial.eval_C,u,v,Fin.prod_univ_succ,
        Fin.cons_zero,Fin.cons_succ,sub_self,zero_mul,sub_zero,zero_sub] at he
      dsimp [signedProduct]
      linear_combination he
    exact mul_left_cancel₀ (sub_ne_zero.mpr hc) hprod

end Field

theorem signedProduct_eq_rat {J : ℕ} {x y : Fin (J+1) → ℚ}
    (hs : ∀ r : ℕ, 1 ≤ r → r ≤ J → signedPower x r=signedPower y r) :
    signedProduct x=signedProduct y :=
  signedProduct_eq_of_signed_powers (fun r hr _ => by exact_mod_cast (show r≠0 by omega)) hs

#print axioms signedProduct_eq_rat
end Waring.SeedCompletionSparseDiagonal
