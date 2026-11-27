import Waring.PolicyCompletionShallowBlock
import Waring.QuadraticHeight

/-!
# Exact literal coefficient-kernel bookkeeping for the shallow estimate

The diagonal, positive off-diagonal pairs, common-denominator partition,
and gcd coordinates are related by exact finite identities.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowActual
open PolicyCompletionBasicMoment PolicyCompletionBasicGcd
open PolicyCompletionShallowArithmetic PolicyCompletionShallowBlock

def positiveFamily (A : Finset ℕ) (H : ℕ) : Finset (ℕ×(ℕ×ℕ)) :=
  Finset.Icc 1 H×ˢlowerPairs A

def positiveKernel (A : Finset ℕ) (k H J : ℕ) (α : ℝ) : ℝ :=
  ∑v∈positiveFamily A H,linearSumBound J (α*(differenceFrequency k v : ℝ))

def divisiblePositiveKernel (A : Finset ℕ) (k H J : ℕ) (r : ℚ) (α : ℝ) : ℝ :=
  ∑v∈(positiveFamily A H).filter (fun v=>r.den∣differenceFrequency k v),
    linearSumBound J (α*(differenceFrequency k v : ℝ))

theorem positiveFamily_bounds {A : Finset ℕ} {H N k : ℕ} (hk : 0<k)
    (hA : A⊆Finset.Icc 1 N) {v : ℕ×(ℕ×ℕ)} (hv : v∈positiveFamily A H) :
    v.2.1<v.2.2 ∧ differenceFrequency k v∈Finset.Icc 1 (H^3*N^(2*k)) := by
  obtain ⟨hh,hp⟩ := Finset.mem_product.mp hv
  obtain ⟨hp,hxy⟩ := Finset.mem_filter.mp hp
  have hy := (Finset.mem_Icc.mp (hA (Finset.mem_product.mp hp).2)).2
  have hf := differenceFrequency_bounds hk (Finset.mem_Icc.mp hh) hxy hy
  exact ⟨hxy,Finset.mem_Icc.mpr hf⟩

theorem positiveKernel_pair_sum (A : Finset ℕ) (k H J : ℕ) (α : ℝ) :
    positiveKernel A k H J α=
      ∑p∈lowerPairs A,∑h∈Finset.Icc 1 H,linearSumBound J (α*pairDifference (2*k) p*(h : ℝ)^3) := by
  unfold positiveKernel positiveFamily
  rw [Finset.sum_product,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro h hh
  have hp' := (Finset.mem_filter.mp hp).2
  have hpow : p.1^(2*k)≤p.2^(2*k) := Nat.pow_le_pow_left hp'.le _
  have hid : α*(differenceFrequency k (h,p) : ℝ)=-(α*pairDifference (2*k) p*(h : ℝ)^3) := by
    dsimp [differenceFrequency,pairDifference]
    rw [Nat.cast_mul,Nat.cast_sub hpow]
    push_cast
    ring
  rw [hid,QuadraticHeight.linearSumBound_neg]

theorem basicMoment_le_positiveKernel (A : Finset ℕ) (k H J : ℕ) (α : ℝ) (σ : ℕ→ℝ) :
    basicMoment A (2*k) H J α σ≤(J : ℝ)*H*A.card+2*positiveKernel A k H J α := by
  have hb := basicMoment_le_pair_kernel A (2*k) H J α σ
  rw [pair_kernel_diagonal,offPairs_sum_eq_twice] at hb
  · rwa [← positiveKernel_pair_sum] at hb
  · intro p
    apply Finset.sum_congr rfl
    intro h hh
    rw [show α*pairDifference (2*k) p.swap*(h : ℝ)^3=
      -(α*pairDifference (2*k) p*(h : ℝ)^3) by dsimp [pairDifference]; ring,
      QuadraticHeight.linearSumBound_neg]

theorem positiveKernel_partition (A : Finset ℕ) (k H J : ℕ) (r : ℚ) (α : ℝ) :
    positiveKernel A k H J α=divisiblePositiveKernel A k H J r α+
      ∑v∈(positiveFamily A H).filter (fun v=>¬r.den∣differenceFrequency k v),
        linearSumBound J (α*(differenceFrequency k v : ℝ)) := by
  exact (Finset.sum_filter_add_sum_filter_not (positiveFamily A H)
    (fun v=>r.den∣differenceFrequency k v)
    (fun v=>linearSumBound J (α*(differenceFrequency k v : ℝ)))).symm

/-- The actual divisible positive pairs are exactly the sum of the fixed
gcd/height blocks already estimated by the shallow source argument. -/
theorem divisiblePositiveKernel_eq_gcd {A : Finset ℕ} {N : ℕ}
    (hA : A⊆Finset.Icc 1 N) (k H J : ℕ) (r : ℚ) (α : ℝ) :
    divisiblePositiveKernel A k H J r α=
      ∑g∈Finset.Icc 1 N,∑h∈Finset.Icc 1 H,divisibleGcdBlock A (2*k) H N J h g r α := by
  unfold divisiblePositiveKernel positiveFamily
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_comm,lowerPairs_sum_eq hA]
  apply Finset.sum_congr rfl
  intro g hg
  have hinner (l : ℕ) :
      (∑n∈quotientDomain A N g l,∑h∈Finset.Icc 1 H,
        if r.den∣differenceFrequency k (h,(g*n,g*(n+l))) then
          linearSumBound J (α*(differenceFrequency k (h,(g*n,g*(n+l))) : ℝ)) else 0)=
      ∑h∈Finset.Icc 1 H,∑n∈quotientDomain A N g l,
        if r.den∣differenceFrequency k (h,(g*n,g*(n+l))) then
          linearSumBound J (α*(differenceFrequency k (h,(g*n,g*(n+l))) : ℝ)) else 0 :=
    Finset.sum_comm
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  unfold divisibleGcdBlock
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [decodedFrequency_eq]

#print axioms basicMoment_le_positiveKernel
#print axioms divisiblePositiveKernel_eq_gcd
end Waring.PolicyCompletionShallowActual
