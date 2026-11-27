import Waring.SeedCompletionEnlargedCross

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEnlargedCross
open SeedCompletionBackward SeedCompletionBackwardCount SeedCompletionBackwardMoments
open SeedCompletionBackwardAggregate SeedCompletionSmall PolicyCompletionHolder
open SeedCompletionSharpBackward PolicyCompletionBackward PolicyCompletionGoodBranch
open PolicyCompletionGoodRecurrence IntegerDifferencePolynomial SmoothMoments

theorem sum_backward_count_le_enlarged {κ ι ν τ : Type*}
    (k : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ)) (w : κ → ℤ)
    (N : ℤ) (Z : κ → Finset ℤ) (B : Finset ι) (U : ι → ℤ)
    (A' : Finset ν) (B' : Finset τ) (f' : ν → ℤ) (U' : τ → ℤ)
    (e : (Σ _ : κ,ℤ × ℤ) → ν) (d : ι → τ)
    (hm : ∀ c ∈ C,∀ p ∈ params c,p.2≠0) (hw : ∀ c ∈ C,0<w c)
    (hZ : ∀ c ∈ C,Z c ⊆ Finset.Icc 1 N)
    (he : Set.InjOn e (↑(aggregateNextDomain C w N k) : Set (Σ _ : κ,ℤ × ℤ)))
    (hd : Set.InjOn d (↑B : Set ι))
    (heA : ∀ a ∈ aggregateNextDomain C w N k,e a∈A')
    (hdB : ∀ b∈B,d b∈B')
    (hef : ∀ a∈aggregateNextDomain C w N k,f' (e a)=aggregateNextPhase k params w a)
    (hdU : ∀ b∈B,U' (d b)=(2:ℤ)^k*U b) :
    (∑ c ∈ C,((stepSolutions k (realParameters (params c)) (w c) (Z c) B
      (fun u => (U u:ℝ))).card : ℝ)) ≤
      (∑ c ∈ C,((Z c).card : ℝ))*secondMoment B U+2*crossIntegral A' f' B' U' := by
  have hsum : (∑ c ∈ C,((stepSolutions k (realParameters (params c)) (w c) (Z c) B
      (fun u => (U u:ℝ))).card : ℝ)) ≤
      (∑ c ∈ C,((Z c).card : ℝ))*secondMoment B U+
        2*∑ c ∈ C,((nextStepSolutions k (realParameters (params c)) (w c) N B
          (fun u => (U u:ℝ))).card : ℝ) := by
    rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c hc
    have h := step_card_le_tuple_diagonal_add_next k (realParameters (params c))
      (w c) N (Z c) B (fun u => (U u:ℝ)) (hw c hc) (hZ c hc)
    rw [crossFrequencyPairs_intCast] at h
    rw [secondMoment_eq_count]
    exact_mod_cast h
  exact hsum.trans (add_le_add_left (mul_le_mul_of_nonneg_left
    (sum_next_step_count_le_enlarged k C params w N B U A' B' f' U' e d hm
      (fun c hc => (hw c hc).ne') he hd heA hdB hef hdU) (by norm_num)) _)

theorem commonModulus_sum_le_enlarged {κ ν τ : Type*} [DecidableEq κ]
    (k s : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ))
    (W : Finset ℕ) (N : ℤ) (Z : Finset ℤ) (Q R : ℝ)
    (A' : Finset ν) (B' : Finset τ) (f' : ν → ℤ) (U' : τ → ℤ)
    (e : (Σ _ : κ × ℕ,ℤ × ℤ) → ν) (d : (Fin s → ℕ) → τ)
    (hm : ∀ c ∈ C,∀ p ∈ params c,p.2≠0)
    (hw : ∀ w∈W,0<w) (hZ : Z ⊆ Finset.Icc 1 N)
    (he : Set.InjOn e (↑(aggregateNextDomain (C ×ˢ W) (fun c => (c.2:ℤ)) N k) :
      Set (Σ _ : κ × ℕ,ℤ × ℤ)))
    (hd : Set.InjOn d (↑(finiteTuples (smoothNumbers Q R) s) : Set (Fin s → ℕ)))
    (heA : ∀ a∈aggregateNextDomain (C ×ˢ W) (fun c => (c.2:ℤ)) N k,e a∈A')
    (hdB : ∀ b∈finiteTuples (smoothNumbers Q R) s,d b∈B')
    (hef : ∀ a∈aggregateNextDomain (C ×ˢ W) (fun c => (c.2:ℤ)) N k,
      f' (e a)=aggregateNextPhase k (fun c => params c.1) (fun c => (c.2:ℤ)) a)
    (hdU : ∀ b∈finiteTuples (smoothNumbers Q R) s,U' (d b)=(2:ℤ)^k*smoothTupleValue k s b) :
    (∑ w∈W,((commonModulusSolutions (C ×ˢ Z) (smoothNumbers Q R)
      (fun c => powerPolynomial k (params c)) s k w).card : ℝ)) ≤
      (C.card:ℝ)*(W.card:ℝ)*(Z.card:ℝ)*smoothMoment k (2*s) Q R+
        2*crossIntegral A' f' B' U' := by
  classical
  have hcount : (∑ w ∈ W,
      ((commonModulusSolutions (C ×ˢ Z) (smoothNumbers Q R)
        (fun c => powerPolynomial k (params c)) s k w).card : ℝ)) =
      ∑ p ∈ C ×ˢ W,
        ((stepSolutions k (realParameters (params p.1)) (p.2 : ℤ) Z
          (finiteTuples (smoothNumbers Q R) s) (fun u => (smoothTupleValue k s u : ℝ))).card : ℝ) := by
    rw [Finset.sum_product,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    exact_mod_cast commonModulus_card_eq_sum_steps C Z (smoothNumbers Q R) params k s w hm
  rw [hcount]
  have H := sum_backward_count_le_enlarged k (C ×ˢ W) (fun p => params p.1)
    (fun p => (p.2 : ℤ)) N (fun _ => Z) (finiteTuples (smoothNumbers Q R) s)
    (smoothTupleValue k s) A' B' f' U' e d
    (fun p hp => hm p.1 (Finset.mem_product.mp hp).1)
    (fun p hp => by
      change (0 : ℤ) < (p.2 : ℤ)
      exact_mod_cast hw p.2 (Finset.mem_product.mp hp).2)
    (fun _ _ => hZ) he hd heA hdB hef hdU
  rw [tuple_secondMoment_eq_smoothMoment] at H
  simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_product,Nat.cast_mul,mul_assoc] using H

#print axioms commonModulus_sum_le_enlarged
end Waring.SeedCompletionEnlargedCross
