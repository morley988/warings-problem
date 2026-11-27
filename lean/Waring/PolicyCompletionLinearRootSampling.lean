import Waring.PolicyCompletionMultiplierHeight
import Waring.CubicRootDivisorClasses

/-!
# Linear-shift resummation for the basic coefficient estimate

The source's integral comparison can be replaced by a finite harmonic
majorant. This preserves the full conductor V*N and costs only a logarithm,
which is absorbed by the usual arbitrary small power loss. Every actual
positive shift and every reduced-denominator divisor class is retained.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionLinearRootSampling
open RationalHeight PolicyCompletionMultiplierHeight CubicDivisorClasses

theorem linear_class_root_term {d n N t E a : ℝ}
    (hd : 1≤d) (hn : 0<n) (ht : 0<t) (hE : 0≤E)
    (ha : 0≤a) (ha1 : a≤1) (hdn : d*n≤N) :
    d^a/(t+E*(d*n))^a≤N/(n*(t+E*N)^a) := by
  have hdp : 0<d := zero_lt_one.trans_le hd
  have hnN : n≤N := (le_mul_of_one_le_left hn.le hd).trans hdn
  have hNp : 0<N := hn.trans_le hnN
  have hl : 0<t+E*(d*n) := by positivity
  have hW : 0<t+E*N := by positivity
  have hbase : d/(t+E*(d*n))≤(N/n)/(t+E*N) := by
    apply (div_le_div_iff₀ hl hW).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_right hdn ht.le
    nlinarith only [hh]
  have hpow := Real.rpow_le_rpow (div_nonneg hdp.le hl.le) hbase ha
  have hNn : 1≤N/n := (one_le_div hn).mpr hnN
  have hpowN : (N/n)^a≤N/n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNn ha1
  calc
    _ ≤ (N/n)^a/(t+E*N)^a := by
      simpa only [Real.div_rpow hdp.le hl.le,
        Real.div_rpow (div_nonneg hNp.le hn.le) hW.le] using hpow
    _ ≤ (N/n)/(t+E*N)^a := div_le_div_of_nonneg_right hpowN (by positivity)
    _ = _ := by ring

def linearClass (N d : ℕ) (t E a : ℝ) : ℝ :=
  ∑h∈(Finset.Icc 1 N).filter (fun h=>d∣h),
    (d : ℝ)^a/(t+E*(h : ℝ))^a

theorem linearClass_bound {N d : ℕ} (hN : 0<N) (hd : 0<d)
    {t E a : ℝ} (ht : 0<t) (hE : 0≤E) (ha : 0≤a) (ha1 : a≤1) :
    linearClass N d t E a≤(N : ℝ)/(t+E*N)^a*(1+Real.log N) := by
  have hd1 : (1 : ℝ)≤d := by exact_mod_cast hd
  have hnR : (0 : ℝ)<N := by exact_mod_cast hN
  have hw : 0≤(N : ℝ)/(t+E*N)^a := by positivity
  have hsum : (∑n∈Finset.range (N/d),1/((n : ℝ)+1))≤1+Real.log (N : ℝ) := by
    calc
      _ ≤ ∑n∈Finset.range N,1/((n : ℝ)+1) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.div_le_self N d)) (fun _ _ _=>by positivity)
      _ = (harmonic N : ℝ) := by simp [harmonic,one_div]
      _ ≤ _ := harmonic_le_one_add_log N
  have hinj : Set.InjOn (fun n=>d*(n+1)) (Finset.range (N/d)) := by
    intro n hn m hm hnm
    have hh := Nat.eq_of_mul_eq_mul_left hd hnm
    omega
  unfold linearClass
  rw [positive_multiples_eq_image N d hd,Finset.sum_image hinj]
  calc
    _ ≤ ∑n∈Finset.range (N/d),
        ((N : ℝ)/(t+E*N)^a)*(1/((n : ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnN : n+1≤N/d := by have := Finset.mem_range.mp hn; omega
      have hdn : d*(n+1)≤N := by
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hnN
      have hh := linear_class_root_term (N := (N : ℝ)) hd1 (by positivity : (0 : ℝ)<(n : ℝ)+1)
        ht hE ha ha1 (by exact_mod_cast hdn)
      convert hh using 1 <;> push_cast <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
    _ = ((N : ℝ)/(t+E*N)^a)*(∑n∈Finset.range (N/d),1/((n : ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hw

/-- The rational matching identity, after passing from max cost to sum cost. -/
theorem matched_height_root_le {r s : ℚ} {n : ℕ} {V α a : ℝ}
    (hV : 0≤V) (ha : 0≤a) (hm : ScaledMatch r s n)
    (hs : cost V (α*(n : ℝ)) s=height V (α*(n : ℝ))) :
    1/(height V (α*(n : ℝ)))^a≤
      2^a*(((r.den/s.den : ℕ) : ℝ)^a/(sumCost (V*(n : ℝ)) α r)^a) := by
  have hc := max_sum_cost_comparison hV (α*(n : ℝ)) s
  rw [hs] at hc
  have hsp : 0<sumCost V (α*(n : ℝ)) s := (height_pos _ _).trans_le hc.1
  have hrec : 1/height V (α*(n : ℝ))≤
      2*(((r.den/s.den : ℕ) : ℝ)/sumCost (V*(n : ℝ)) α r) := by
    calc
      _ ≤ 2/sumCost V (α*(n : ℝ)) s :=
        (div_le_div_iff₀ (height_pos _ _) hsp).mpr (by simpa using hc.2)
      _ = _ := by
        rw [show 2/sumCost V (α*(n : ℝ)) s=2*(1/sumCost V (α*(n : ℝ)) s) by ring,
          scaled_reciprocal hm]
  have hden : 0≤sumCost (V*(n : ℝ)) α r := by
    unfold sumCost
    have he := error_nonneg α r
    change 0≤(r.den : ℝ)+(V*(n : ℝ))*error α r
    positivity
  have hp := Real.rpow_le_rpow (div_nonneg zero_le_one (height_pos _ _).le) hrec ha
  rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2)
    (div_nonneg (Nat.cast_nonneg (r.den/s.den)) hden),
    Real.div_rpow (Nat.cast_nonneg (r.den/s.den)) hden] at hp
  simpa only [Real.div_rpow zero_le_one (height_pos _ _).le,Real.one_rpow] using hp

theorem linear_reciprocal_root_with_approximant (N : ℕ) (r : ℚ)
    {V Z α a : ℝ} (hN : 0<N) (hV : 0<V) (hZ : 0<Z)
    (ha : 0≤a) (ha1 : a≤1)
    (hsmall : (N : ℝ)*Z*error α r+(r.den : ℝ)*Z/V<1) :
    (∑n∈Finset.Icc 1 N,1/(height V (α*(n : ℝ)))^a)≤
      (N : ℝ)/Z^a+2^a*(r.den.divisors.card : ℝ)*
        ((N : ℝ)/(sumCost (V*N) α r)^a)*(1+Real.log N) := by
  choose s hs using (fun n : ℕ=>exists_minimizer hV (α*(n : ℝ)))
  let weight : ℕ→ℕ→ℝ := fun d n=>
    if d∣n then (d : ℝ)^a/(sumCost (V*(n : ℝ)) α r)^a else 0
  have hcost (n : ℕ) : 0≤sumCost (V*(n : ℝ)) α r := by
    change 0≤(r.den : ℝ)+(V*(n : ℝ))*error α r
    exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg hV.le (Nat.cast_nonneg n)) (error_nonneg α r))
  have hw (d n : ℕ) : 0≤weight d n := by
    dsimp [weight]
    split_ifs
    · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Real.rpow_nonneg (hcost n) _)
    · exact le_rfl
  have hpoint (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      1/(height V (α*(n : ℝ)))^a≤1/Z^a+2^a*∑d∈r.den.divisors,weight d n := by
    by_cases hshort : height V (α*(n : ℝ))<Z
    · have hm := scaled_match_of_short_height r (s n) hV hZ.le
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
        (by rw [hs n]; exact hshort.le) hsmall
      have hc := scaled_denominator_class hm
      have hdmem : r.den/(s n).den∈r.den.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hc.1,r.den_nz⟩
      have hsingle := Finset.single_le_sum (fun d _=>hw d n) hdmem
      have hbound := matched_height_root_le hV.le ha hm (hs n)
      have hh : 1/(height V (α*(n : ℝ)))^a≤2^a*∑d∈r.den.divisors,weight d n := by
        exact hbound.trans (mul_le_mul_of_nonneg_left
          (by simpa only [weight,if_pos hc.2] using hsingle) (by positivity))
      exact hh.trans (le_add_of_nonneg_left (by positivity))
    · have hh : 1/(height V (α*(n : ℝ)))^a≤1/Z^a :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hZ _)
          (Real.rpow_le_rpow hZ.le (le_of_not_gt hshort) ha)
      exact hh.trans (le_add_of_nonneg_right
        (mul_nonneg (by positivity) (Finset.sum_nonneg (fun d _=>hw d n))))
  have hclass (d : ℕ) (hd : d∈r.den.divisors) :
      (∑n∈Finset.Icc 1 N,weight d n)≤
        (N : ℝ)/(sumCost (V*N) α r)^a*(1+Real.log N) := by
    have hid : (∑n∈Finset.Icc 1 N,weight d n)=linearClass N d (r.den : ℝ) (V*error α r) a := by
      simp only [weight,← Finset.sum_filter,linearClass,sumCost,error]
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
      ring
    rw [hid]
    have hb := linearClass_bound hN (Nat.pos_of_mem_divisors hd)
      (show (0 : ℝ)<r.den by exact_mod_cast r.pos) (mul_nonneg hV.le (error_nonneg α r)) ha ha1
    convert hb using 1 <;> unfold sumCost error <;> ring
  calc
    _ ≤ ∑n∈Finset.Icc 1 N,(1/Z^a+2^a*∑d∈r.den.divisors,weight d n) :=
      Finset.sum_le_sum hpoint
    _ = (N : ℝ)/Z^a+2^a*∑d∈r.den.divisors,∑n∈Finset.Icc 1 N,weight d n := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
      simp [div_eq_mul_inv]
    _ ≤ (N : ℝ)/Z^a+2^a*∑_d∈r.den.divisors,
        (N : ℝ)/(sumCost (V*N) α r)^a*(1+Real.log N) := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hclass) (by positivity)) _
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The linear resummation with its rational witness constructed. -/
theorem linear_reciprocal_root_bound (N : ℕ) {V Z α a : ℝ}
    (hN : 0<N) (hV : 0<V) (hVN : 1≤V*N) (hZ : 0<Z)
    (ha : 0≤a) (ha1 : a≤1) (hsize : 2*Z*Real.sqrt (V*N)/V<1) :
    ∃r : ℚ,cost (V*N) α r=height (V*N) α ∧
      (∑n∈Finset.Icc 1 N,1/(height V (α*(n : ℝ)))^a)≤
        (N : ℝ)/Z^a+2^a*(r.den.divisors.card : ℝ)*
          ((N : ℝ)/(height (V*N) α)^a)*(1+Real.log N) := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  obtain ⟨r,hr⟩ := exists_minimizer (mul_pos hV hNR) α
  have hsmall := minimizer_small_cross hV hNR hVN hZ.le r hr hsize
  have hb := linear_reciprocal_root_with_approximant N r hN hV hZ ha ha1 hsmall
  refine ⟨r,hr,hb.trans ?_⟩
  have hc := (max_sum_cost_comparison (mul_nonneg hV.le hNR.le) α r).1
  rw [hr] at hc
  have hlog : 0≤1+Real.log (N : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ)≤N by exact_mod_cast hN)
    linarith
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ hlog
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div_of_nonneg_left hNR.le (Real.rpow_pos_of_pos (height_pos _ _) _)
    (Real.rpow_le_rpow (height_pos _ _).le hc ha)

#print axioms linearClass_bound
#print axioms linear_reciprocal_root_bound
end Waring.PolicyCompletionLinearRootSampling
