import Waring.PolicyCompletionBasicMoment
import Waring.PolicyCompletionBinomialArithmetic

/-!
# The exact gcd decomposition in the basic coefficient estimate

Positive unequal coefficient pairs are parametrized by their gcd and two
coprime translated endpoints. The finite identity keeps the original block
membership, so the subsequent binomial quotient bounds apply to the actual
off-diagonal sum, with no multiplicity or support assumption.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicGcd
open RationalHeight PolicyCompletionBasicMoment PolicyCompletionBinomialArithmetic

theorem cost_neg (V α : ℝ) (r : ℚ) : cost V (-α) (-r)=cost V α r := by
  simp only [cost,Rat.den_neg_eq_den,Rat.num_neg_eq_neg_num,Int.cast_neg]
  congr 2
  rw [show (r.den : ℝ)*(-α)-(-(r.num : ℝ)) = -((r.den : ℝ)*α-(r.num : ℝ)) by ring,
    abs_neg]

theorem height_neg (V α : ℝ) : height V (-α)=height V α := by
  unfold height
  congr 1
  ext x
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨-r,by simpa only [neg_neg] using (cost_neg V α (-r)).symm⟩
  · rintro ⟨r,rfl⟩
    exact ⟨-r,cost_neg V α r⟩

def lowerPairs (A : Finset ℕ) : Finset (ℕ×ℕ) :=
  (A×ˢA).filter fun p=>p.1<p.2

def quotientDomain (A : Finset ℕ) (N j l : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N/j)).filter fun n=>
    Nat.Coprime n (n+l) ∧ n+l≤N/j ∧ j*n∈A ∧ j*(n+l)∈A

def gcdDomain (A : Finset ℕ) (N : ℕ) : Finset (Σj : ℕ,Σl : ℕ,ℕ) :=
  (Finset.Icc 1 N).sigma fun j=>
    (Finset.Icc 1 (N/j)).sigma fun l=>quotientDomain A N j l

def decode (u : Σj : ℕ,Σl : ℕ,ℕ) : ℕ×ℕ :=
  (u.1*u.2.2,u.1*(u.2.2+u.2.1))

theorem mem_gcdDomain {A : Finset ℕ} {N j l n : ℕ} :
    (⟨j,⟨l,n⟩⟩ : Σj : ℕ,Σl : ℕ,ℕ)∈gcdDomain A N ↔
      (1≤j ∧ j≤N) ∧ (1≤l ∧ l≤N/j) ∧ (1≤n ∧ n≤N/j) ∧
        Nat.Coprime n (n+l) ∧ n+l≤N/j ∧ j*n∈A ∧ j*(n+l)∈A := by
  simp [gcdDomain,quotientDomain,Finset.mem_sigma,and_assoc]

theorem decode_mem {A : Finset ℕ} {N : ℕ} {u : Σj : ℕ,Σl : ℕ,ℕ}
    (hu : u∈gcdDomain A N) : decode u∈lowerPairs A := by
  obtain ⟨j,l,n⟩ := u
  obtain ⟨hj,hl,hn,hcop,hbound,ha,hb⟩ := mem_gcdDomain.mp hu
  change (j*n,j*(n+l))∈lowerPairs A
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨ha,hb⟩,
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)⟩

theorem decode_gcd {A : Finset ℕ} {N : ℕ} {u : Σj : ℕ,Σl : ℕ,ℕ}
    (hu : u∈gcdDomain A N) : (decode u).1.gcd (decode u).2=u.1 := by
  obtain ⟨j,l,n⟩ := u
  obtain ⟨hj,hl,hn,hcop,hbound,ha,hb⟩ := mem_gcdDomain.mp hu
  simpa [decode,Nat.gcd_mul_left,hcop.gcd_eq_one]

theorem decode_injective {A : Finset ℕ} {N : ℕ} :
    Set.InjOn decode (gcdDomain A N : Set (Σj : ℕ,Σl : ℕ,ℕ)) := by
  intro u hu v hv heq
  have hj : u.1=v.1 := by
    rw [← decode_gcd hu,← decode_gcd hv,heq]
  obtain ⟨j,l,n⟩ := u
  obtain ⟨j',l',n'⟩ := v
  dsimp at hj
  subst j'
  have hjpos : 0<j := by have := (mem_gcdDomain.mp hu).1.1; omega
  have hn : n=n' := Nat.eq_of_mul_eq_mul_left hjpos (congrArg Prod.fst heq)
  subst n'
  have hl : n+l=n+l' := Nat.eq_of_mul_eq_mul_left hjpos (congrArg Prod.snd heq)
  have hll : l=l' := by omega
  subst l'
  rfl

theorem decode_surjective {A : Finset ℕ} {N : ℕ} (hA : A⊆Finset.Icc 1 N)
    {p : ℕ×ℕ} (hp : p∈lowerPairs A) :
    ∃u∈gcdDomain A N,decode u=p := by
  obtain ⟨hpA,hlt⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpA
  have haB := Finset.mem_Icc.mp (hA ha)
  have hbB := Finset.mem_Icc.mp (hA hb)
  let j := p.1.gcd p.2
  let n := p.1/j
  let t := p.2/j
  have hj : 0<j := Nat.gcd_pos_of_pos_left _ (by omega)
  have hjn : j*n=p.1 := by
    simpa [j,n,mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)
  have hjt : j*t=p.2 := by
    simpa [j,t,mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_right p.1 p.2)
  have hn : 0<n := by
    apply Nat.pos_of_ne_zero
    intro hz
    have : p.1=0 := by rw [← hjn,hz,mul_zero]
    omega
  have hnt : n<t := by
    apply (Nat.mul_lt_mul_left hj).mp
    simpa only [hjn,hjt] using hlt
  have htB : t≤N/j := Nat.div_le_div_right hbB.2
  have hjB : j≤N :=
    (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left p.1 p.2)).trans haB.2
  have hnt' : n+(t-n)=t := Nat.add_sub_of_le hnt.le
  refine ⟨⟨j,⟨t-n,n⟩⟩,mem_gcdDomain.mpr ?_,?_⟩
  · refine ⟨⟨hj,hjB⟩,⟨by omega,by omega⟩,⟨hn,by omega⟩,?_,?_,?_,?_⟩
    · rw [hnt']
      exact Nat.coprime_div_gcd_div_gcd hj
    · simpa [hnt'] using htB
    · simpa [hjn] using ha
    · simpa [hnt',hjt] using hb
  · simp only [decode,hnt',hjn,hjt,Prod.mk.eta]

theorem lowerPairs_sum_eq {A : Finset ℕ} {N : ℕ} (hA : A⊆Finset.Icc 1 N)
    (f : ℕ×ℕ→ℝ) :
    (∑p∈lowerPairs A,f p)=
      ∑j∈Finset.Icc 1 N,∑l∈Finset.Icc 1 (N/j),
        ∑n∈quotientDomain A N j l,f (j*n,j*(n+l)) := by
  calc
    _ = ∑u∈gcdDomain A N,f (decode u) := by
      symm
      apply Finset.sum_bij (fun u _=>decode u)
      · exact fun _ hu=>decode_mem hu
      · exact fun _ hu _ hv h=>decode_injective hu hv h
      · intro p hp
        obtain ⟨u,hu,heq⟩ := decode_surjective hA hp
        exact ⟨u,hu,heq⟩
      · exact fun _ _=>rfl
    _ = _ := by simp only [gcdDomain,Finset.sum_sigma,decode]

theorem offPairs_sum_eq_twice (A : Finset ℕ) (f : ℕ×ℕ→ℝ)
    (hsymm : ∀p,f p.swap=f p) :
    (∑p∈offPairs A,f p)=2*∑p∈lowerPairs A,f p := by
  have hsplit (p : ℕ×ℕ) :
      (if p.1≠p.2 then f p else 0)=
        (if p.1<p.2 then f p else 0)+(if p.2<p.1 then f p else 0) := by
    rcases lt_trichotomy p.1 p.2 with h|h|h
    · simp [h,h.ne,Nat.not_lt_of_ge h.le]
    · simp [h]
    · simp [h,h.ne',Nat.not_lt_of_ge h.le]
  have hswap : (∑p∈(A×ˢA).filter (fun p=>p.2<p.1),f p)=
      ∑p∈lowerPairs A,f p := by
    apply Finset.sum_bij (fun p _=>p.swap)
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb,ha⟩,hlt⟩
    · exact fun _ _ _ _ h=>Prod.swap_injective h
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      exact ⟨p.swap,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb,ha⟩,hlt⟩,
        Prod.swap_swap p⟩
    · exact fun p _=>(hsymm p).symm
  calc
    _ = ∑p∈A×ˢA,((if p.1<p.2 then f p else 0)+(if p.2<p.1 then f p else 0)) := by
      rw [offPairs,Finset.sum_filter]
      exact Finset.sum_congr rfl fun p _=>hsplit p
    _ = (∑p∈lowerPairs A,f p)+∑p∈(A×ˢA).filter (fun p=>p.2<p.1),f p := by
      rw [Finset.sum_add_distrib]
      simp only [lowerPairs,Finset.sum_filter]
    _ = _ := by rw [hswap]; ring

theorem real_difference_eq_quotient (d n l : ℕ) :
    ((n : ℝ)+l)^d-(n : ℝ)^d=(l : ℝ)*(natQuotient d n l : ℝ) := by
  rw [← geom_sum₂_mul]
  simp only [natQuotient,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_add]
  rw [show (n : ℝ)+l-n=l by ring]
  ring

theorem decode_difference (d j l n : ℕ) :
    pairDifference d (j*n,j*(n+l))=
      -((j : ℝ)^d*l*(natQuotient d n l : ℝ)) := by
  dsimp [pairDifference]
  push_cast
  rw [mul_pow,mul_pow]
  calc
    _ = -((j : ℝ)^d*(((n : ℝ)+l)^d-(n : ℝ)^d)) := by ring
    _ = _ := by rw [real_difference_eq_quotient]; ring

theorem offPairs_height_gcd (A : Finset ℕ) {N : ℕ} (hA : A⊆Finset.Icc 1 N)
    (d : ℕ) (V α a : ℝ) :
    (∑p∈offPairs A,1/(height V (α*pairDifference d p))^a)=
      2*∑j∈Finset.Icc 1 N,∑l∈Finset.Icc 1 (N/j),
        ∑n∈quotientDomain A N j l,
          1/(height V ((α*(j : ℝ)^d*l)*(natQuotient d n l : ℝ)))^a := by
  rw [offPairs_sum_eq_twice]
  · rw [lowerPairs_sum_eq hA]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro n hn
    rw [decode_difference]
    rw [show α*(-((j : ℝ)^d*l*(natQuotient d n l : ℝ)))=
      -((α*(j : ℝ)^d*l)*(natQuotient d n l : ℝ)) by ring,height_neg]
  · intro p
    rw [show α*pairDifference d p.swap=-(α*pairDifference d p) by
      dsimp [pairDifference]; ring,height_neg]

theorem quotientDomain_bounds {A : Finset ℕ} {N j l n : ℕ} {M : ℝ}
    (hj : 0<j) (hA : ∀m∈A,M<(m : ℝ)) (hn : n∈quotientDomain A N j l) :
    M/(j : ℝ)<(n : ℝ) ∧ ((n+l : ℕ) : ℝ)≤(N : ℝ)/j := by
  obtain ⟨hn,hcop,hbound,ha,hb⟩ := Finset.mem_filter.mp hn
  have hjR : (0 : ℝ)<j := by exact_mod_cast hj
  constructor
  · apply (div_lt_iff₀ hjR).mpr
    simpa only [Nat.cast_mul,mul_comm] using hA _ ha
  · apply (le_div_iff₀ hjR).mpr
    have hnat := (Nat.le_div_iff_mul_le hj).mp hbound
    exact_mod_cast hnat

#print axioms lowerPairs_sum_eq
#print axioms offPairs_height_gcd
end Waring.PolicyCompletionBasicGcd
