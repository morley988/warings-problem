import Waring.PolicyCompletionBinomialArithmetic
import Waring.PolicyCompletionBasicGcd

/-!
# Arithmetic fibers for the shallow basic coefficient estimate

These are the actual frequency and congruence fibers in Vaughan (1989),
Lemma3.2, as used by Vaughan--Wooley (1995), Lemma4.2.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowArithmetic
open PolicyCompletionBinomialArithmetic PolicyCompletionBinomialRoots

def differenceFrequency (k : ℕ) (v : ℕ×(ℕ×ℕ)) : ℕ :=
  v.1^3*(v.2.2^(2*k)-v.2.1^(2*k))

def divisorEncoding (k : ℕ) (v : ℕ×(ℕ×ℕ)) : ℕ×(ℕ×ℕ) :=
  (v.1,(v.2.2^k-v.2.1^k,v.2.2^k+v.2.1^k))

theorem differenceFrequency_factor (k : ℕ) (v : ℕ×(ℕ×ℕ)) :
    differenceFrequency k v=v.1^3*((v.2.2^k-v.2.1^k)*(v.2.2^k+v.2.1^k)) := by
  dsimp [differenceFrequency]
  rw [show 2*k=k*2 by omega,pow_mul,pow_mul,Nat.sq_sub_sq]
  ring

theorem divisorEncoding_injective {k : ℕ} (hk : 0<k)
    {u v : ℕ×(ℕ×ℕ)} (hu : u.2.1≤u.2.2) (hv : v.2.1≤v.2.2)
    (he : divisorEncoding k u=divisorEncoding k v) : u=v := by
  have hh := congrArg Prod.fst he
  have hm := congrArg (fun w : ℕ×(ℕ×ℕ)=>w.2.1) he
  have hp := congrArg (fun w : ℕ×(ℕ×ℕ)=>w.2.2) he
  dsimp [divisorEncoding] at hh hm hp
  have hu' := Nat.pow_le_pow_left hu k
  have hv' := Nat.pow_le_pow_left hv k
  have hx : u.2.1^k=v.2.1^k := by omega
  have hy : u.2.2^k=v.2.2^k := by omega
  exact Prod.ext hh (Prod.ext (Nat.pow_left_injective hk.ne' hx)
    (Nat.pow_left_injective hk.ne' hy))

/-- Three actual divisors determine the height and the two endpoints. -/
theorem differenceFrequency_fiber_card_le {k : ℕ} (hk : 0<k)
    (S : Finset (ℕ×(ℕ×ℕ))) (hS : ∀v∈S,v.2.1<v.2.2)
    {t : ℕ} (ht : 0<t) :
    (S.filter fun v=>differenceFrequency k v=t).card≤t.divisors.card^3 := by
  have hc : (S.filter fun v=>differenceFrequency k v=t).card≤
      (t.divisors×ˢ(t.divisors×ˢt.divisors)).card := by
    apply Finset.card_le_card_of_injOn (divisorEncoding k)
    · intro v hv
      obtain ⟨hv,hfreq⟩ := Finset.mem_filter.mp hv
      have hf : v.1^3*((v.2.2^k-v.2.1^k)*(v.2.2^k+v.2.1^k))=t := by
        rwa [differenceFrequency_factor] at hfreq
      have hheight : v.1∣t := hf ▸ (dvd_mul_of_dvd_left (dvd_pow_self v.1 (by norm_num : 3≠0)) _)
      have hminus : v.2.2^k-v.2.1^k∣t := hf ▸
        (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
      have hplus : v.2.2^k+v.2.1^k∣t := hf ▸
        (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
      exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hheight,ht.ne'⟩,
        Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hminus,ht.ne'⟩,
          Nat.mem_divisors.mpr ⟨hplus,ht.ne'⟩⟩⟩
    · intro u hu v hv he
      exact divisorEncoding_injective hk (hS u (Finset.mem_filter.mp hu).1).le
        (hS v (Finset.mem_filter.mp hv).1).le he
  simpa only [Finset.card_product,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hc

theorem differenceFrequency_fiber_le_rpow {k : ℕ} (hk : 0<k) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀S : Finset (ℕ×(ℕ×ℕ)),(∀v∈S,v.2.1<v.2.2)→
      ∀t : ℕ,0<t→((S.filter fun v=>differenceFrequency k v=t).card : ℝ)≤C*(t : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow 3 hε
  refine ⟨C,hC,?_⟩
  intro S hS t ht
  exact (show ((S.filter fun v=>differenceFrequency k v=t).card : ℝ)≤
    (t.divisors.card : ℝ)^3 by exact_mod_cast differenceFrequency_fiber_card_le hk S hS ht).trans
      (hdiv t ht)

theorem differenceFrequency_bounds {k H N : ℕ} (hk : 0<k)
    {v : ℕ×(ℕ×ℕ)} (hh : 1≤v.1 ∧ v.1≤H) (hxy : v.2.1<v.2.2)
    (hy : v.2.2≤N) : 0<differenceFrequency k v ∧ differenceFrequency k v≤H^3*N^(2*k) := by
  constructor
  · exact Nat.mul_pos (pow_pos hh.1 _) (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hxy (by omega)))
  · exact Nat.mul_le_mul (Nat.pow_le_pow_left hh.2 _)
      ((Nat.sub_le _ _).trans (Nat.pow_le_pow_left hy _))

/-- Actual frequency grouping for arbitrary nonnegative weights, with the
small-power multiplicity supplied by the proved divisor injection. -/
theorem weighted_differenceFrequency_grouping {k : ℕ} (hk : 0<k) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : ℕ,∀S : Finset (ℕ×(ℕ×ℕ)),∀F : ℕ→ℝ,
      (∀v∈S,v.2.1<v.2.2)→
      (∀v∈S,differenceFrequency k v∈Finset.Icc 1 T)→
      (∀t∈Finset.Icc 1 T,0≤F t)→
      (∑v∈S,F (differenceFrequency k v))≤C*(T : ℝ)^ε*∑t∈Finset.Icc 1 T,F t := by
  obtain ⟨C,hC,hfiber⟩ := differenceFrequency_fiber_le_rpow hk hε
  refine ⟨C,hC,?_⟩
  intro T S F hS hmap hF
  rw [← Finset.sum_fiberwise_of_maps_to' hmap F]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨htp,htT⟩ := Finset.mem_Icc.mp ht
  have htTR : (t : ℝ)≤(T : ℝ) := by exact_mod_cast htT
  have hh := (hfiber S hS t htp).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) htTR hε.le) hC.le)
  exact mul_le_mul_of_nonneg_right hh (hF t ht)

theorem difference_eq_shift_quotient (d n l : ℕ) :
    (n+l)^d-n^d=l*natQuotient d n l := by
  have hp : n^d≤(n+l)^d := Nat.pow_le_pow_left (Nat.le_add_right _ _) _
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sub hp]
  simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_mul,natQuotient,Nat.cast_sum]
  rw [← geom_sum₂_mul]
  have he : (n : ℤ)+(l : ℤ)-(n : ℤ)=(l : ℤ) := by ring
  rw [he]
  ring

theorem quotient_dvd_after_gcd {q l D : ℕ} (hq : 0<q) (hdiv : q∣l*D) :
    q/q.gcd l∣D := by
  have hg : 0<q.gcd l := Nat.gcd_pos_of_pos_left l hq
  have hqeq : q.gcd l*(q/q.gcd l)=q := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hleq : q.gcd l*(l/q.gcd l)=l := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hmul : q.gcd l*(q/q.gcd l)∣q.gcd l*((l/q.gcd l)*D) := by
    simpa only [← mul_assoc,hqeq,hleq] using hdiv
  exact (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left
    (Nat.dvd_of_mul_dvd_mul_left hg hmul)

/-- The unreduced difference congruence is reduced to the genuine
divided-difference fiber by the exact gcd of its shift and modulus. -/
theorem power_difference_fiber_card_le_rpow {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀q l N : ℕ,0<q→0<l→∀A : Finset ℕ,
      A⊆Finset.Icc 1 N→(∀n∈A,Nat.Coprime n (n+l))→
      ((A.filter fun n=>q∣(n+l)^d-n^d).card : ℝ)≤
        C*((N : ℝ)/((q/q.gcd l : ℕ) : ℝ)+1)*((l*(q/q.gcd l) : ℕ) : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := natQuotient_fiber_card_le_rpow hd hε
  refine ⟨C,hC,?_⟩
  intro q l N hq hl A hA hcop
  have hg : 0<q.gcd l := Nat.gcd_pos_of_pos_left l hq
  have hquot : 0<q/q.gcd l := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left _ _)) hg
  have hsub : A.filter (fun n=>q∣(n+l)^d-n^d)⊆
      A.filter (fun n=>q/q.gcd l∣natQuotient d n l) := by
    intro n hn
    obtain ⟨hn,hdiv⟩ := Finset.mem_filter.mp hn
    rw [difference_eq_shift_quotient] at hdiv
    exact Finset.mem_filter.mpr ⟨hn,quotient_dvd_after_gcd hq hdiv⟩
  exact (show ((A.filter fun n=>q∣(n+l)^d-n^d).card : ℝ)≤
    ((A.filter fun n=>q/q.gcd l∣natQuotient d n l).card : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans (hbound _ l N hquot hl A hA hcop)

#print axioms differenceFrequency_fiber_le_rpow
#print axioms weighted_differenceFrequency_grouping
#print axioms power_difference_fiber_card_le_rpow
end Waring.PolicyCompletionShallowArithmetic
