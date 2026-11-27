import Waring.AuxiliaryCounting
import Waring.EvenMoments
import Mathlib.Tactic.FinCases

/-!
# The unconditional fourth-moment seed

The exact Fourier count for the fourth moment embeds into the actual two-block
power-difference zero-sum family with h=1. The established divisor proof bounds
that count by C_epsilon P^(2+epsilon), uniformly in the smoothness cutoff.
No published moment estimate or abstract admissibility assumption is used.
-/

noncomputable section
open scoped BigOperators
namespace Waring.FourthMomentSeed
open PowerDifferenceFibers AuxiliaryCounting SmoothMoments

private def pairToBlocks (p : (Fin 2 → ℕ) × (Fin 2 → ℕ)) : List Block :=
  [⟨1,p.1 1,p.2 1⟩,⟨1,p.1 0,p.2 0⟩]

private theorem pairToBlocks_injective : Function.Injective pairToBlocks := by
  intro p q hpq
  have h1 := (List.cons.inj hpq).1
  have h0 := (List.cons.inj (List.cons.inj hpq).2).1
  apply Prod.ext
  · funext i
    fin_cases i
    · exact congrArg Block.m h0
    · exact congrArg Block.m h1
  · funext i
    fin_cases i
    · exact congrArg Block.n h0
    · exact congrArg Block.n h1

private theorem mem_extendFamily {S : Finset (List Block)} {B : Finset Block}
    {xs : List Block} {x : Block} (hxs : xs ∈ S) (hx : x ∈ B) :
    x::xs ∈ extendFamily S B := by
  exact Finset.mem_image.mpr ⟨(xs,x),Finset.mem_product.mpr ⟨hxs,hx⟩,rfl⟩

/-- A literal injection of fourth-moment solutions into the two-block count. -/
theorem equalSumPairs_four_card_le (k N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    (equalSumPairs A (fun n => ((n^k : ℕ) : ℤ)) 2).card ≤
      zeroCount k (prefixFamily (fun _ => 1) (fun _ => N) 2) := by
  apply Finset.card_le_card_of_injOn pairToBlocks ?_ (fun _ _ _ _ h => pairToBlocks_injective h)
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp,hzero⟩
  rcases Finset.mem_product.mp hp with ⟨hl,hr⟩
  have hl' : ∀ i : Fin 2, p.1 i ∈ A := by simpa only [finiteTuples,Fintype.mem_piFinset] using hl
  have hr' : ∀ i : Fin 2, p.2 i ∈ A := by simpa only [finiteTuples,Fintype.mem_piFinset] using hr
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_extendFamily
    · apply mem_extendFamily
      · exact Finset.mem_singleton_self []
      · exact mem_blockRange.mpr ⟨by simp,hA (hl' 0),hA (hr' 0)⟩
    · exact mem_blockRange.mpr ⟨by simp,hA (hl' 1),hA (hr' 1)⟩
  · simp only [Fin.sum_univ_two] at hzero
    simp only [pairToBlocks,sumValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      blockValue,Nat.cast_one,one_pow,one_mul,add_zero]
    push_cast at hzero
    linarith

/-- The fourth moment of the actual smooth sum has the full exponent two,
uniformly in every real smoothness cutoff R, without any cutoff hypothesis. -/
theorem smoothMoment_four_le (k : ℕ) (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ R : ℝ,
      smoothMoment k 4 P R ≤ C*P^(2+ε) := by
  classical
  obtain ⟨C,hC,hcount⟩ := auxiliary_zeroCount_le_polynomial 2
    (show (0 : ℝ) ≤ k by positivity) hε
  refine ⟨C,hC,?_⟩
  intro P hP R
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hN : 1 ≤ ⌊P⌋₊ := by exact Nat.floor_pos.mpr hP
  have hsize : ∀ i < 2, (((1 : ℕ)^2*⌊P⌋₊^k : ℕ) : ℝ) ≤ P^(k : ℝ) := by
    intro i hi
    simp only [one_pow,one_mul,Nat.cast_pow,Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) (Nat.floor_le hP0) k
  have hparam : ∀ i < 2, (∏ _j ∈ Finset.range i, ⌊P⌋₊) ≤ 1*⌊P⌋₊ := by
    intro i hi
    interval_cases i <;> simp [hN]
  have haux := hcount P hP k hk (fun _ => 1) (fun _ => ⌊P⌋₊) hsize hparam
  have hdiag : diagonalProduct (fun _ => 1) (fun _ => ⌊P⌋₊) 2 = ⌊P⌋₊^2 := by
    simp [diagonalProduct,pow_two]
  rw [hdiag,Nat.cast_pow] at haux
  calc
    smoothMoment k 4 P R =
        ((equalSumPairs (smoothNumbers P R) (fun n => ((n^k : ℕ) : ℤ)) 2).card : ℝ) :=
      smoothMoment_even_eq_card k 2 P R
    _ ≤ (zeroCount k (prefixFamily (fun _ => 1) (fun _ => ⌊P⌋₊) 2) : ℝ) := by
      exact_mod_cast equalSumPairs_four_card_le k ⌊P⌋₊ (smoothNumbers P R)
        (Finset.filter_subset _ _)
    _ ≤ C*P^ε*(⌊P⌋₊ : ℝ)^2 := haux
    _ ≤ C*P^ε*P^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (Nat.floor_le hP0) 2) (by positivity)
    _ = C*P^(2+ε) := by
      rw [show (P^2 : ℝ)=P^(2 : ℝ) from (Real.rpow_natCast P 2).symm,
        mul_assoc,← Real.rpow_add (lt_of_lt_of_le zero_lt_one hP)]
      congr 2
      ring

/-- Genuine fourth-moment admissibility, retaining all common-smoothness
quantifiers and providing an unconditional coefficient seed for degrees 16/18. -/
theorem admissibleExponent_four {k : ℕ} (hk : 2 ≤ k) : AdmissibleExponent k 4 2 := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := smoothMoment_four_le k hk hε
  exact ⟨1,zero_lt_one,C,hC,1,le_rfl,fun P hP R _hR _hRP => hbound P hP R⟩

theorem coefficient16_four : AdmissibleExponent 16 4 2 :=
  admissibleExponent_four (by norm_num)

theorem coefficient18_four : AdmissibleExponent 18 4 2 :=
  admissibleExponent_four (by norm_num)

#print axioms equalSumPairs_four_card_le
#print axioms smoothMoment_four_le
#print axioms admissibleExponent_four
end Waring.FourthMomentSeed
