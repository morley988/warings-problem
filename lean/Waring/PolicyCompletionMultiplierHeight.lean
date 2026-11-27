import Waring.CubicExceptionalSampling
import Waring.PolicyCompletionBinomialRoots

/-!
# Rational-height resummation over structured integer multipliers

The same reduced-fraction rigidity applies to the divided differences and
ordinary shifts in Vaughan--Wooley (1995), Lemma4.3.  This file proves the
finite common-approximant reduction and retains the exact divisibility
fibers, so that the preceding coprime quotient count can be substituted.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionMultiplierHeight
open RationalHeight CubicExceptionalSampling PolicyCompletionBinomialRoots

def ScaledMatch (r s : ℚ) (n : ℕ) : Prop :=
  r.num*(n : ℤ)*(s.den : ℤ)=s.num*(r.den : ℤ)

theorem scaled_denominator_class {r s : ℚ} {n : ℕ} (hm : ScaledMatch r s n) :
    s.den∣r.den ∧ (r.den/s.den)∣n := by
  have hs : (s.den : ℤ)≠0 := by exact_mod_cast s.den_nz
  have hst : (s.den : ℤ)∣(r.den : ℤ) := by
    apply (rat_isCoprime s).symm.dvd_of_dvd_mul_left
    rw [← hm]
    exact dvd_mul_left _ _
  have htns : (r.den : ℤ)∣(n : ℤ)*(s.den : ℤ) := by
    apply (rat_isCoprime r).symm.dvd_of_dvd_mul_left
    rw [← mul_assoc,hm]
    exact dvd_mul_left _ _
  have hquot : ((r.den : ℤ)/(s.den : ℤ))∣(n : ℤ) := by
    obtain ⟨t,ht⟩ := hst
    have hdiv : t∣(n : ℤ) := by
      apply (mul_dvd_mul_iff_left hs).mp
      simpa only [ht,mul_comm (n : ℤ) (s.den : ℤ)] using htns
    simpa only [ht,Int.mul_ediv_cancel_left _ hs] using hdiv
  constructor
  · exact_mod_cast hst
  · exact_mod_cast hquot

theorem scaled_sumCost {r s : ℚ} {n : ℕ} (hm : ScaledMatch r s n)
    (V α : ℝ) :
    sumCost V (α*(n : ℝ)) s=(s.den : ℝ)*
      (1+(V*error α r/(r.den : ℝ))*(n : ℝ)) := by
  have ht : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have hc : (r.num : ℝ)*(n : ℝ)*(s.den : ℝ)=(s.num : ℝ)*(r.den : ℝ) := by
    exact_mod_cast hm
  have heq : (s.den : ℝ)*(α*(n : ℝ))-(s.num : ℝ)=
      ((s.den : ℝ)*(n : ℝ)/(r.den : ℝ))*((r.den : ℝ)*α-(r.num : ℝ)) := by
    field_simp
    nlinarith [hc]
  have he : error (α*(n : ℝ)) s=
      ((s.den : ℝ)*(n : ℝ)/(r.den : ℝ))*error α r := by
    unfold error
    rw [heq,abs_mul,abs_of_nonneg (by positivity)]
  change (s.den : ℝ)+V*error (α*(n : ℝ)) s=_
  rw [he]
  ring

theorem scaled_reciprocal {r s : ℚ} {n : ℕ} (hm : ScaledMatch r s n)
    (V α : ℝ) :
    1/sumCost V (α*(n : ℝ)) s=
      ((r.den/s.den : ℕ) : ℝ)/sumCost (V*(n : ℝ)) α r := by
  have hdiv := (scaled_denominator_class hm).1
  have ht : (r.den : ℝ)≠0 := by exact_mod_cast r.den_nz
  have hs : (s.den : ℝ)≠0 := by exact_mod_cast s.den_nz
  have hprod : ((r.den/s.den : ℕ) : ℝ)*(s.den : ℝ)=(r.den : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hdiv
  rw [scaled_sumCost hm]
  change 1/((s.den : ℝ)*(1+(V*error α r/(r.den : ℝ))*(n : ℝ)))=
    ((r.den/s.den : ℕ) : ℝ)/((r.den : ℝ)+(V*(n : ℝ))*error α r)
  have hid : (s.den : ℝ)*(1+(V*error α r/(r.den : ℝ))*(n : ℝ))=
      (s.den : ℝ)/(r.den : ℝ)*((r.den : ℝ)+(V*(n : ℝ))*error α r) := by field_simp
  rw [hid,← one_div_mul_one_div,one_div_div]
  have hratio : (r.den : ℝ)/(s.den : ℝ)=((r.den/s.den : ℕ) : ℝ) :=
    (div_eq_iff hs).mpr hprod.symm
  rw [hratio]
  ring

theorem scaled_match_of_short_height {V Z U α : ℝ} {n : ℕ} (r s : ℚ)
    (hV : 0<V) (hZ : 0≤Z) (hnU : (n : ℝ)≤U)
    (hs : cost V (α*(n : ℝ)) s≤Z)
    (hsmall : U*Z*error α r+(r.den : ℝ)*Z/V<1) : ScaledMatch r s n := by
  have ht : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have hsden : (s.den : ℝ)≤Z := (le_max_left _ _).trans hs
  have hserr : error (α*(n : ℝ)) s≤Z/V := by
    apply (le_div_iff₀ hV).mpr
    simpa only [cost,error,mul_comm] using (le_max_right _ _).trans hs
  have hU : 0≤U := (Nat.cast_nonneg n).trans hnU
  have hb : (n : ℝ)*(s.den : ℝ)*error α r+(r.den : ℝ)*error (α*(n : ℝ)) s<1 := by
    have hfirst := mul_le_mul_of_nonneg_right
      (mul_le_mul hnU hsden (by positivity) hU) (error_nonneg α r)
    have hsecond := mul_le_mul_of_nonneg_left hserr ht.le
    rw [← mul_div_assoc] at hsecond
    linarith
  have hid : ((r.num*(n : ℤ)*(s.den : ℤ)-s.num*(r.den : ℤ) : ℤ) : ℝ)=
      -((n : ℝ)*(s.den : ℝ))*((r.den : ℝ)*α-(r.num : ℝ))+
      (r.den : ℝ)*((α*(n : ℝ))*(s.den : ℝ)-(s.num : ℝ)) := by
    push_cast
    ring
  apply sub_eq_zero.mp
  apply SamplingArithmetic.int_eq_zero_of_abs_cast_lt_one
  rw [hid]
  apply (abs_add_le _ _).trans_lt
  simpa only [abs_mul,abs_neg,abs_of_nonneg (show (0 : ℝ)≤(n : ℝ)*(s.den : ℝ) by positivity),
    abs_of_pos ht,error,mul_comm (α*(n : ℝ)) (s.den : ℝ)] using hb

/-- The elementary weighted divisor term; both the length contribution and
the extra endpoint are retained. -/
theorem divisor_weight_le {a d W N : ℝ} (ha : 0≤a) (ha1 : a≤1)
    (hd : 1≤d) (hdW : d≤W) (hN : 0≤N) :
    (N/d+1)*(d^a/W^a)≤N/W^a+1 := by
  have hdp : 0<d := zero_lt_one.trans_le hd
  have hWp : 0<W := hdp.trans_le hdW
  have hWa : 0<W^a := Real.rpow_pos_of_pos hWp _
  have hda : d^a≤d := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd ha1
  have hdWa : d^a≤W^a := Real.rpow_le_rpow hdp.le hdW ha
  have hfirst : N/d*d^a≤N := by
    calc
      _ ≤ N/d*d := mul_le_mul_of_nonneg_left hda (div_nonneg hN hdp.le)
      _ = N := div_mul_cancel₀ _ hdp.ne'
  have hsum : (N/d+1)*d^a≤N+W^a := by nlinarith only [hfirst,hdWa]
  have hh := div_le_div_of_nonneg_right hsum hWa.le
  convert hh using 1 <;> field_simp <;> ring

/-- Finite structured-multiplier estimate. The only fiber premise counts
actual divisibility in the displayed finite domain. It will be discharged
by the proved binomial quotient and ordinary interval counts. -/
theorem structured_reciprocal_bound {ι : Type*} (A : Finset ι) (f : ι→ℕ) (r : ℚ)
    {V Z L U α a N K : ℝ} (hV : 0<V) (hZ : 0<Z) (hL : 0≤L)
    (ha : 0≤a) (ha1 : a≤1) (hN : 0≤N) (hK : 0≤K)
    (hlo : ∀x∈A,L≤(f x : ℝ)) (hup : ∀x∈A,(f x : ℝ)≤U)
    (hsmall : U*Z*error α r+(r.den : ℝ)*Z/V<1)
    (hcount : ∀d∈r.den.divisors,
      ((A.filter fun x=>d∣f x).card : ℝ)≤K*(N/(d : ℝ)+1)) :
    (∑x∈A,1/(height V (α*(f x : ℝ)))^a)≤
      (A.card : ℝ)/Z^a+2^a*K*(r.den.divisors.card : ℝ)*
        (N/(sumCost (V*L) α r)^a+1) := by
  classical
  let W := sumCost (V*L) α r
  have ht : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have htW : (r.den : ℝ)≤W := by
    change (r.den : ℝ)≤(r.den : ℝ)+(V*L)*error α r
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hV.le hL) (error_nonneg α r))
  have hWp : 0<W := ht.trans_le htW
  have hWa : 0<W^a := Real.rpow_pos_of_pos hWp _
  choose s hs using (fun x : ι => exists_minimizer hV (α*(f x : ℝ)))
  let weight : ℕ→ι→ℝ := fun d x => if d∣f x then (d : ℝ)^a/W^a else 0
  have hw (d : ℕ) (x : ι) : 0≤weight d x := by
    dsimp [weight]
    split_ifs <;> positivity
  have hshort (x : ι) (hx : x∈A) (hshort : height V (α*(f x : ℝ))<Z) :
      1/(height V (α*(f x : ℝ)))^a≤
        2^a*∑d∈r.den.divisors,weight d x := by
    have hm : ScaledMatch r (s x) (f x) := scaled_match_of_short_height r (s x)
      hV hZ.le (hup x hx) (by rw [hs x]; exact hshort.le) hsmall
    let d := r.den/(s x).den
    have hdmem : d∈r.den.divisors := Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd (scaled_denominator_class hm).1,r.den_nz⟩
    have hdn : d∣f x := (scaled_denominator_class hm).2
    have hdpos : 0<d := Nat.pos_of_mem_divisors hdmem
    have hdR : (0 : ℝ)<d := by exact_mod_cast hdpos
    have hlocal := max_sum_cost_comparison hV.le (α*(f x : ℝ)) (s x)
    rw [hs x] at hlocal
    have hlocalpos : 0<sumCost V (α*(f x : ℝ)) (s x) :=
      (height_pos _ _).trans_le hlocal.1
    have hrec : 1/height V (α*(f x : ℝ))≤2*((d : ℝ)/W) := by
      have hcW : W≤sumCost (V*(f x : ℝ)) α r := by
        change (r.den : ℝ)+(V*L)*error α r≤(r.den : ℝ)+(V*(f x : ℝ))*error α r
        exact add_le_add_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlo x hx) hV.le) (error_nonneg α r)) _
      calc
        _ ≤ 2/sumCost V (α*(f x : ℝ)) (s x) :=
          (div_le_div_iff₀ (height_pos _ _) hlocalpos).mpr (by simpa using hlocal.2)
        _ = 2*((d : ℝ)/sumCost (V*(f x : ℝ)) α r) := by
          rw [show 2/sumCost V (α*(f x : ℝ)) (s x)=
            2*(1/sumCost V (α*(f x : ℝ)) (s x)) by ring,scaled_reciprocal hm]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hdR.le hWp hcW) (by norm_num)
    have hpow := Real.rpow_le_rpow
      (div_nonneg zero_le_one (height_pos V (α*(f x : ℝ))).le) hrec ha
    have hpow' : 1/(height V (α*(f x : ℝ)))^a≤2^a*((d : ℝ)^a/W^a) := by
      simpa only [Real.div_rpow zero_le_one (height_pos _ _).le,Real.one_rpow,
        Real.mul_rpow (by norm_num : (0 : ℝ)≤2) (div_nonneg hdR.le hWp.le),
        Real.div_rpow hdR.le hWp.le] using hpow
    apply hpow'.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
    have hsingle := Finset.single_le_sum (fun d _ => hw d x) hdmem
    simpa only [weight,if_pos hdn] using hsingle
  have hpoint (x : ι) (hx : x∈A) :
      1/(height V (α*(f x : ℝ)))^a≤
        1/Z^a+2^a*∑d∈r.den.divisors,weight d x := by
    by_cases hh : height V (α*(f x : ℝ))<Z
    · exact (hshort x hx hh).trans (le_add_of_nonneg_left (by positivity))
    · have hlarge : 1/(height V (α*(f x : ℝ)))^a≤1/Z^a :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hZ _)
          (Real.rpow_le_rpow hZ.le (le_of_not_gt hh) ha)
      exact hlarge.trans (le_add_of_nonneg_right
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Finset.sum_nonneg (fun d _ => hw d x))))
  have hfiber (d : ℕ) (hd : d∈r.den.divisors) :
      (∑x∈A,weight d x)≤K*(N/W^a+1) := by
    have hd1 : (1 : ℝ)≤d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hdW : (d : ℝ)≤W :=
      (show (d : ℝ)≤r.den by exact_mod_cast Nat.le_of_dvd r.pos (Nat.dvd_of_mem_divisors hd)).trans htW
    calc
      _ = ((A.filter fun x=>d∣f x).card : ℝ)*((d : ℝ)^a/W^a) := by
        simp only [weight,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      _ ≤ (K*(N/(d : ℝ)+1))*((d : ℝ)^a/W^a) :=
        mul_le_mul_of_nonneg_right (hcount d hd) (by positivity)
      _ = K*((N/(d : ℝ)+1)*((d : ℝ)^a/W^a)) := by ring
      _ ≤ K*(N/W^a+1) := mul_le_mul_of_nonneg_left
        (divisor_weight_le ha ha1 hd1 hdW hN) hK
  calc
    _ ≤ ∑x∈A,(1/Z^a+2^a*∑d∈r.den.divisors,weight d x) := Finset.sum_le_sum hpoint
    _ = (A.card : ℝ)/Z^a+2^a*∑d∈r.den.divisors,∑x∈A,weight d x := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ (A.card : ℝ)/Z^a+2^a*∑_d∈r.den.divisors,K*(N/W^a+1) := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfiber) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,W]
      ring

/-- A minimizing fraction at conductor V*U satisfies every local rigidity
test below the explicit square-root cutoff. -/
theorem minimizer_small_cross {V U Z α : ℝ} (hV : 0<V) (hU : 0<U)
    (hVU : 1≤V*U) (hZ : 0≤Z) (r : ℚ)
    (hr : cost (V*U) α r=height (V*U) α)
    (hsize : 2*Z*Real.sqrt (V*U)/V<1) :
    U*Z*error α r+(r.den : ℝ)*Z/V<1 := by
  have hprod : 0<V*U := mul_pos hV hU
  have hc : cost (V*U) α r≤Real.sqrt (V*U) := hr ▸ height_le_sqrt hVU α
  have hd : (r.den : ℝ)≤Real.sqrt (V*U) := (le_max_left _ _).trans hc
  have he : error α r≤Real.sqrt (V*U)/(V*U) := by
    apply (le_div_iff₀ hprod).mpr
    simpa only [cost,error,mul_comm] using (le_max_right _ _).trans hc
  have hfirst : U*Z*error α r≤Z*Real.sqrt (V*U)/V := by
    calc
      _ ≤ U*Z*(Real.sqrt (V*U)/(V*U)) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hU.le hZ)
      _ = _ := by field_simp
  have hsecond : (r.den : ℝ)*Z/V≤Z*Real.sqrt (V*U)/V := by
    calc
      _ ≤ Real.sqrt (V*U)*Z/V := by gcongr
      _ = _ := by ring
  calc
    _ ≤ Z*Real.sqrt (V*U)/V+Z*Real.sqrt (V*U)/V := add_le_add hfirst hsecond
    _ = 2*Z*Real.sqrt (V*U)/V := by ring
    _ < 1 := hsize

#print axioms scaled_denominator_class
#print axioms scaled_match_of_short_height
#print axioms structured_reciprocal_bound
#print axioms minimizer_small_cross
end Waring.PolicyCompletionMultiplierHeight
