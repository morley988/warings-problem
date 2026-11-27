import Waring.PolicyCompletionEvenLowDegreePairs

/-! # Uniform small-power bounds for the actual low-degree pair counts -/
noncomputable section
namespace Waring.PolicyCompletionEvenLowDegreeBounds
open PolicyCompletionEvenLowDegreePairs

theorem divisor_pair_bound {B K ε : ℝ} (hB : 0≤B) (hK : 0<K) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀n : ℤ,n≠0→(n.natAbs:ℝ)≤K*P^B→
      (2*(n.natAbs.divisors.card:ℝ))≤C*P^ε := by
  let δ : ℝ:=ε/(B+1)
  have hδ : 0<δ:=div_pos hε (by linarith)
  have hBδ : B*δ≤ε:=by
    have hh : δ*(B+1)=ε:=div_mul_cancel₀ ε (by linarith)
    nlinarith
  obtain ⟨D,hD,hdiv⟩:=DivisorBound.divisor_count_le_rpow hδ
  refine ⟨2*D*K^δ,by positivity,?_⟩
  intro P hP n hn hnP
  have hPp : 0<P:=zero_lt_one.trans_le hP
  calc
    _ ≤ 2*(D*(n.natAbs:ℝ)^δ):=mul_le_mul_of_nonneg_left
      (hdiv _ (Int.natAbs_pos.mpr hn)) (by norm_num)
    _ ≤ 2*(D*(K*P^B)^δ):=by gcongr
    _ = (2*D*K^δ)*P^(B*δ):=by
      rw [Real.mul_rpow hK.le (Real.rpow_nonneg hPp.le _),←Real.rpow_mul hPp.le]
      ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hBδ) (by positivity)

theorem quarticDiscriminant_natAbs_le {a b c d e : ℤ} {S : ℝ} (hS : 0≤S)
    (ha : |(a:ℝ)|≤S) (hb : |(b:ℝ)|≤S) (hc : |(c:ℝ)|≤S)
    (hd : |(d:ℝ)|≤S) (he : |(e:ℝ)|≤S) :
    ((quarticDiscriminant a b c d e).natAbs:ℝ)≤10*S^2 := by
  have habs (n : ℤ) : (n.natAbs:ℝ)=|(n:ℝ)|:=by
    have hh:=congrArg (fun z : ℤ=>(z:ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast,Int.cast_abs] using hh
  rw [habs]
  simp only [quarticDiscriminant,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  calc
    _ ≤ |(b:ℝ)^2-(d:ℝ)^2|+|4*(a:ℝ)*((c:ℝ)-(e:ℝ))|:=abs_sub _ _
    _ ≤ (|(b:ℝ)|^2+|(d:ℝ)|^2)+4*|(a:ℝ)| *(|(c:ℝ)|+|(e:ℝ)|):=by
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤4)]
      apply add_le_add
      · have ht : |(b:ℝ)^(2:ℕ)-(d:ℝ)^(2:ℕ)|≤
            |(b:ℝ)^(2:ℕ)|+|(d:ℝ)^(2:ℕ)|:=abs_sub _ _
        simpa only [pow_two,abs_mul] using ht
      · exact mul_le_mul_of_nonneg_left (abs_sub (c:ℝ) (e:ℝ)) (by positivity)
    _ ≤ (S^2+S^2)+4*S*(S+S):=by gcongr
    _ = _:=by ring

theorem difference_natAbs_le {a b : ℤ} {S : ℝ}
    (ha : |(a:ℝ)|≤S) (hb : |(b:ℝ)|≤S) : ((a-b).natAbs:ℝ)≤2*S := by
  have hcast : ((a-b).natAbs:ℝ)=|((a-b:ℤ):ℝ)|:=by
    have hh:=congrArg (fun z : ℤ=>(z:ℝ)) (Int.natCast_natAbs (a-b))
    simpa only [Int.cast_natCast,Int.cast_abs] using hh
  rw [hcast,Int.cast_sub]
  exact (abs_sub (a:ℝ) (b:ℝ)).trans (by linarith)

theorem quartic_unequal_uniform {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀a b c d e : ℤ,
      0<a→0≤b→0≤d→
      |(a:ℝ)|≤P^B→|(b:ℝ)|≤P^B→|(c:ℝ)|≤P^B→|(d:ℝ)|≤P^B→|(e:ℝ)|≤P^B→
      ¬(b=d ∧ c=e)→∀Z W : Finset ℤ,(∀z∈Z,0<z)→(∀w∈W,0<w)→
      ((quarticPairs a b c d e Z W).card:ℝ)≤C*P^ε := by
  obtain ⟨C,hC,hdiv⟩:=divisor_pair_bound (B:=2*B) (K:=10) (by positivity) (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro P hP a b c d e ha hb hd haP hbP hcP hdP heP hne Z W hZ hW
  have hS : 1≤P^B:=Real.one_le_rpow hP hB
  have hpower : (P^B)^2=P^(2*B):=by
    rw [←Real.rpow_mul_natCast (zero_le_one.trans hP)]
    congr 1
    norm_num
    ring
  by_cases hdisc : quarticDiscriminant a b c d e=0
  · have hdb : d-b≠0:=by
      intro heq
      have hbd : b=d:=(sub_eq_zero.mp heq).symm
      apply hne
      refine ⟨hbd,?_⟩
      unfold quarticDiscriminant at hdisc
      rw [hbd,sub_self,zero_sub] at hdisc
      have hh : 4*a*(c-e)=0:=by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by positivity))
    have hbound : ((d-b).natAbs:ℝ)≤10*P^(2*B):=by
      rw [←hpower]
      exact (difference_natAbs_le hdP hbP).trans (by nlinarith)
    have hc : ((quarticPairs a b c d e Z W).card:ℝ)≤2*((d-b).natAbs.divisors.card:ℝ):=by
      exact_mod_cast quarticPairs_discriminant_zero_card_le ha hb hd hne Z W hZ hW hdisc
    exact hc.trans (hdiv P hP (d-b) hdb hbound)
  · have hbound : ((quarticDiscriminant a b c d e).natAbs:ℝ)≤10*P^(2*B):=by
      rw [←hpower]
      exact quarticDiscriminant_natAbs_le (zero_le_one.trans hS) haP hbP hcP hdP heP
    have hc : ((quarticPairs a b c d e Z W).card:ℝ)≤
        2*((quarticDiscriminant a b c d e).natAbs.divisors.card:ℝ):=by
      exact_mod_cast quarticPairs_discriminant_ne_card_le ha Z W hZ hW hdisc
    exact hc.trans (hdiv P hP _ hdisc hbound)

theorem quadratic_unequal_uniform {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀a c e : ℤ,a≠0→
      |(c:ℝ)|≤P^B→|(e:ℝ)|≤P^B→c≠e→∀Z W : Finset ℤ,
      ((quadraticPairs a c e Z W).card:ℝ)≤C*P^ε := by
  obtain ⟨C,hC,hdiv⟩:=divisor_pair_bound (B:=B) (K:=2) hB (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro P hP a c e ha hc he hne Z W
  have hbound:=difference_natAbs_le he hc
  have hh : ((quadraticPairs a c e Z W).card:ℝ)≤2*((e-c).natAbs.divisors.card:ℝ):=by
    exact_mod_cast quadraticPairs_unequal_card_le ha hne Z W
  exact hh.trans (hdiv P hP _ (sub_ne_zero.mpr hne.symm) hbound)

#print axioms quartic_unequal_uniform
#print axioms quadratic_unequal_uniform
end Waring.PolicyCompletionEvenLowDegreeBounds
