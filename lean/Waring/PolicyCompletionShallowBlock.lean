import Waring.PolicyCompletionShallowPairs
import Waring.PolicyCompletionShallowKernel
import Waring.PolicyCompletionBasicLinear

/-!
# Actual divisible coefficient pairs in a fixed gcd and height block

The source congruence and the real error weight are verified on the literal
gcd decomposition of the coefficient set. Every support enlargement is a
finite subset inclusion, with the original strict lower cutoff retained.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowBlock
open RationalHeight PolicyCompletionBasicGcd PolicyCompletionShallowArithmetic
open PolicyCompletionBinomialArithmetic PolicyCompletionShallowPairs
open PolicyCompletionShallowKernel PolicyCompletionShallowSpacing

def decodedFrequency (d h g l n : ℕ) : ℕ :=
  h^3*g^d*((n+l)^d-n^d)

theorem decodedFrequency_eq (k h g l n : ℕ) :
    decodedFrequency (2*k) h g l n=differenceFrequency k (h,(g*n,g*(n+l))) := by
  dsimp [decodedFrequency,differenceFrequency]
  rw [mul_pow,mul_pow,← Nat.mul_sub_left_distrib]
  ring

theorem decodedFrequency_quotient (d h g l n : ℕ) :
    decodedFrequency d h g l n=h^3*g^d*l*natQuotient d n l := by
  rw [decodedFrequency,difference_eq_shift_quotient]
  ring

theorem decodedFrequency_lower {d g : ℕ} (hd : 0<d) (hg : 0<g)
    {M : ℝ} (hM : 0≤M) (h l n : ℕ) (hMn : M≤(g*n : ℕ)) :
    (h : ℝ)^3*g*M^(d-1)*l≤(decodedFrequency d h g l n : ℝ) := by
  have hnQ : n^(d-1)≤natQuotient d n l := by
    have hh := (natQuotient_bounds d n l).1
    have hd1 : 1≤d := hd
    nlinarith
  have hMn' : M≤(g : ℝ)*(n : ℝ) := by simpa only [Nat.cast_mul] using hMn
  have hpoly : (g : ℝ)*M^(d-1)≤(g : ℝ)^d*(natQuotient d n l : ℝ) := by
    calc
      _ ≤ (g : ℝ)*((g : ℝ)*(n : ℝ))^(d-1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM hMn' _) (by positivity)
      _ = (g : ℝ)^d*(n : ℝ)^(d-1) := by
        rw [mul_pow,← mul_assoc,← pow_succ',Nat.sub_add_cancel hd]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hnQ) (by positivity)
  rw [decodedFrequency_quotient]
  push_cast
  have hh := mul_le_mul_of_nonneg_left hpoly (show 0≤(h : ℝ)^3*(l : ℝ) by positivity)
  nlinarith only [hh]

def divisibleGcdBlock (A : Finset ℕ) (d H N J h g : ℕ) (r : ℚ) (α : ℝ) : ℝ :=
  ∑l∈Finset.Icc 1 (N/g),
    ∑n∈(quotientDomain A N g l).filter (fun n=>r.den∣decodedFrequency d h g l n),
      linearSumBound J (α*(decodedFrequency d h g l n : ℝ))

/-- Literal fixed-height, fixed-gcd block, before the final denominator
averaging. The sole rational approximation premise is constructed by
Dirichlet at the full frequency range in the final source theorem. -/
theorem divisible_gcd_block_bound {k : ℕ} (hk : 0<k) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀A : Finset ℕ,∀H N J h g : ℕ,
      (A⊆Finset.Icc 1 N)→(1≤h ∧ h≤H)→(1≤g ∧ g≤N)→
      ∀M : ℝ,0≤M→(∀m∈A,M<(m : ℝ))→∀r : ℚ,∀α : ℝ,
      2*((H^3*N^(2*k) : ℕ) : ℝ)*error α r≤1→
      let L : ℕ := N/g+1
      let q : ℕ := r.den/(r.den.gcd (h^3*g^(2*k)))
      let B := (J : ℝ)*|α-(r : ℝ)| *(h : ℝ)^3*g*M^(2*k-1)
      divisibleGcdBlock A (2*k) H N J h g r α≤
        2*(J : ℝ)*C*((L*q : ℕ) : ℝ)^ε*
          (((L : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log L))/(q*(1+B*(L : ℝ)))+L) := by
  obtain ⟨C,hC,hpairs⟩ := primitive_pair_weighted_bound (by omega : 0<2*k) hε
  refine ⟨C,hC,?_⟩
  intro A H N J h g hA hh hg M hM hlow r α herr
  dsimp only
  let L : ℕ := N/g+1
  let q : ℕ := r.den/(r.den.gcd (h^3*g^(2*k)))
  let B := (J : ℝ)*|α-(r : ℝ)| *(h : ℝ)^3*g*M^(2*k-1)
  have hq : 0<q := Nat.div_pos (Nat.le_of_dvd r.pos (Nat.gcd_dvd_left _ _))
    (Nat.gcd_pos_of_pos_left _ r.pos)
  have hL : (0 : ℕ)<L := Nat.succ_pos _
  have hB : 0≤B := by dsimp [B]; positivity
  have hsub (l : ℕ) :
      (quotientDomain A N g l).filter (fun n=>r.den∣decodedFrequency (2*k) h g l n)⊆
        primitiveShiftSet (2*k) q l L := by
    intro n hn
    obtain ⟨hn,hdiv⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hcop,hbound,ha,hb⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,?_⟩,hcop,?_⟩
    · have hh := (Finset.mem_Icc.mp hn).2
      dsimp [L]
      omega
    · exact quotient_dvd_after_gcd r.pos hdiv
  have hpoint (l n : ℕ)
      (hn : n∈(quotientDomain A N g l).filter (fun n=>r.den∣decodedFrequency (2*k) h g l n)) :
      linearSumBound J (α*(decodedFrequency (2*k) h g l n : ℝ))≤
        2*(J : ℝ)/(1+B*(l : ℝ)) := by
    obtain ⟨hn,hdiv⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn',hcop,hbound,ha,hb⟩ := Finset.mem_filter.mp hn
    have hfreq : decodedFrequency (2*k) h g l n≤H^3*N^(2*k) := by
      dsimp [decodedFrequency]
      have hy := (Finset.mem_Icc.mp (hA hb)).2
      have hpow : g^(2*k)*(n+l)^(2*k)≤N^(2*k) := by
        simpa only [← mul_pow] using Nat.pow_le_pow_left hy (2*k)
      calc
        _ ≤ h^3*(g^(2*k)*(n+l)^(2*k)) := by
          have hh' := Nat.mul_le_mul_left (h^3*g^(2*k)) (Nat.sub_le ((n+l)^(2*k)) (n^(2*k)))
          simpa only [mul_assoc] using hh'
        _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_left hh.2 _) hpow
    have hnear : (decodedFrequency (2*k) h g l n : ℝ)*error α r≤1/2 := by
      have hf : (decodedFrequency (2*k) h g l n : ℝ)≤((H^3*N^(2*k) : ℕ) : ℝ) := by exact_mod_cast hfreq
      have hh' := mul_le_mul_of_nonneg_right hf (error_nonneg α r)
      linarith
    have hkernel := divisible_linear_kernel_le r hdiv hnear J
    have hlower := decodedFrequency_lower (by omega : 0<2*k) hg.1 hM h l n (hlow _ ha).le
    have hden : B*(l : ℝ)≤(J : ℝ)*|α-(r : ℝ)| *(decodedFrequency (2*k) h g l n : ℝ) := by
      have hh' := mul_le_mul_of_nonneg_left hlower (show 0≤(J : ℝ)*|α-(r : ℝ)| by positivity)
      dsimp [B]
      nlinarith only [hh']
    exact hkernel.trans (div_le_div_of_nonneg_left (by positivity)
      (show 0<1+B*(l : ℝ) by positivity) (add_le_add_left hden 1))
  have hlocal (l : ℕ) :
      (∑n∈(quotientDomain A N g l).filter (fun n=>r.den∣decodedFrequency (2*k) h g l n),
        linearSumBound J (α*(decodedFrequency (2*k) h g l n : ℝ)))≤
        2*(J : ℝ)*((primitiveShiftSet (2*k) q l L).card : ℝ)/(1+B*(l : ℝ)) := by
    calc
      _ ≤ ∑_n∈(quotientDomain A N g l).filter (fun n=>r.den∣decodedFrequency (2*k) h g l n),
          2*(J : ℝ)/(1+B*(l : ℝ)) := Finset.sum_le_sum fun n hn=>hpoint l n hn
      _ ≤ (primitiveShiftSet (2*k) q l L).card*(2*(J : ℝ)/(1+B*(l : ℝ))) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (hsub l)
      _ = _ := by ring
  have hlsub : Finset.Icc 1 (N/g)⊆Finset.Icc 1 L := Finset.Icc_subset_Icc_right (by dsimp [L]; omega)
  calc
    divisibleGcdBlock A (2*k) H N J h g r α≤
        ∑l∈Finset.Icc 1 (N/g),2*(J : ℝ)*((primitiveShiftSet (2*k) q l L).card : ℝ)/(1+B*(l : ℝ)) :=
      Finset.sum_le_sum fun l _=>hlocal l
    _ ≤ ∑l∈Finset.Icc 1 L,2*(J : ℝ)*((primitiveShiftSet (2*k) q l L).card : ℝ)/(1+B*(l : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hlsub (fun l _ _=>by positivity)
    _ = 2*(J : ℝ)*∑l∈Finset.Icc 1 L,((primitiveShiftSet (2*k) q l L).card : ℝ)/(1+B*(l : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ 2*(J : ℝ)*(C*((L*q : ℕ) : ℝ)^ε*
        (((L : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log L))/(q*(1+B*(L : ℝ)))+L)) :=
      mul_le_mul_of_nonneg_left (hpairs q L hq hL B hB) (by positivity)
    _ = _ := by ring

#print axioms decodedFrequency_lower
#print axioms divisible_gcd_block_bound
end Waring.PolicyCompletionShallowBlock
