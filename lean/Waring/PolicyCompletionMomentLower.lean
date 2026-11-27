import Waring.SeedCompletionBackwardCount
import Waring.SmoothProductDensity
import Waring.PolicyCompletionSmallSmooth

/-! # Actual lower bounds for smooth even moments

The diagonal tuples and finite Cauchy over the possible power sums give
both elementary lower bounds. These statements concern the literal
finite smooth set and the exact Fourier moment, without a density premise.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionMomentLower
open SeedCompletionBackwardCount SmoothMoments

theorem diagonal_card_le {ι γ : Type*} (A : Finset ι) (f : ι → γ) :
    A.card ≤ (crossFrequencyPairs A A f f).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun x => (x,x))
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hx⟩,rfl⟩
  · intro x hx y hy he
    exact congrArg Prod.fst he

theorem card_sq_le_range_mul_collisions {ι γ : Type*}
    (A : Finset ι) (N : Finset γ) (f : ι → γ)
    (hf : ∀ x ∈ A,f x ∈ N) :
    (A.card : ℝ)^2 ≤ (N.card : ℝ)*(crossFrequencyPairs A A f f).card := by
  classical
  have hcross : (crossFrequencyPairs A N f id).card=A.card := by
    symm
    apply Finset.card_bij (fun x _ => (x,f x))
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hf x hx⟩,rfl⟩
    · intro x hx y hy he
      exact congrArg Prod.fst he
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,he⟩
      exact ⟨p.1,(Finset.mem_product.mp hp).1,Prod.ext rfl he⟩
  have hdiag : (crossFrequencyPairs N N id id).card=N.card := by
    symm
    apply Finset.card_bij (fun x _ => (x,x))
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hx⟩,rfl⟩
    · intro x hx y hy he
      exact congrArg Prod.fst he
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,he⟩
      exact ⟨p.1,(Finset.mem_product.mp hp).1,Prod.ext rfl he⟩
  have h := crossFrequencyPairs_card_sq_le A N f id
  rw [hcross,hdiag,mul_comm] at h
  exact h

/-- Every diagonal ordered tuple contributes one solution. -/
theorem smooth_card_pow_le_moment (k r : ℕ) (P R : ℝ) :
    ((smoothNumbers P R).card : ℝ)^r ≤ smoothMoment k (2*r) P R := by
  rw [smoothMoment_even_eq_card]
  have h := diagonal_card_le (finiteTuples (smoothNumbers P R) r)
    (fun u => ∑ i,((u i)^k : ℕ) : (Fin r → ℕ) → ℕ)
  have he : crossFrequencyPairs (finiteTuples (smoothNumbers P R) r)
      (finiteTuples (smoothNumbers P R) r) (fun u => ∑ i,(u i)^k)
      (fun u => ∑ i,(u i)^k) =
      equalSumPairs (smoothNumbers P R) (fun n => ((n^k : ℕ) : ℤ)) r := by
    ext p
    simp only [crossFrequencyPairs,equalSumPairs,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨hp,he⟩
      exact ⟨hp,by exact_mod_cast he⟩
    · rintro ⟨hp,he⟩
      exact ⟨hp,by exact_mod_cast he⟩
  rw [he] at h
  simpa [finiteTuples,Fintype.card_piFinset] using (show
    ((finiteTuples (smoothNumbers P R) r).card : ℝ) ≤
    ((equalSumPairs (smoothNumbers P R) (fun n => ((n^k : ℕ) : ℤ)) r).card : ℝ) by
      exact_mod_cast h)

/-- Finite Cauchy, using only the range of an ordered sum of powers. -/
theorem smooth_card_pow_le_range_moment (k r : ℕ) {P : ℝ} (R : ℝ)
    (hP : 1 ≤ P) :
    ((smoothNumbers P R).card : ℝ)^(2*r) ≤
      ((r : ℝ)+1)*P^k*smoothMoment k (2*r) P R := by
  classical
  let A := finiteTuples (smoothNumbers P R) r
  let f : (Fin r → ℕ) → ℕ := fun u => ∑ i,(u i)^k
  let N := Finset.range (r*⌊P⌋₊^k+1)
  have hf : ∀ u ∈ A,f u ∈ N := by
    intro u hu
    apply Finset.mem_range.mpr
    have hu' : ∀ i : Fin r,u i ≤ ⌊P⌋₊ := by
      intro i
      exact (mem_smoothNumbers.mp ((Fintype.mem_piFinset.mp hu) i)).1.2
    have hb : f u ≤ r*⌊P⌋₊^k := by
      calc
        _ ≤ ∑ _i : Fin r,⌊P⌋₊^k :=
          Finset.sum_le_sum (fun i _ => Nat.pow_le_pow_left (hu' i) k)
        _ = _ := by simp
    exact Nat.lt_succ_of_le hb
  have hc := card_sq_le_range_mul_collisions A N f hf
  have he : crossFrequencyPairs A A f f =
      equalSumPairs (smoothNumbers P R) (fun n => ((n^k : ℕ) : ℤ)) r := by
    ext p
    simp only [crossFrequencyPairs,equalSumPairs,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨hp,he⟩
      exact ⟨hp,by dsimp [f] at he; exact_mod_cast he⟩
    · rintro ⟨hp,he⟩
      exact ⟨hp,by dsimp [f]; exact_mod_cast he⟩
  rw [he,← smoothMoment_even_eq_card] at hc
  have hA : (A.card : ℝ)^2=((smoothNumbers P R).card : ℝ)^(2*r) := by
    simp [A,finiteTuples,Fintype.card_piFinset,← pow_mul,Nat.mul_comm r 2]
  rw [hA] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (smoothMoment_nonneg _ _ _ _)
  have hfloor : (⌊P⌋₊ : ℝ)^k ≤ P^k := pow_le_pow_left₀ (by positivity) (Nat.floor_le (by linarith)) k
  have hpow : (1 : ℝ) ≤ P^k := one_le_pow₀ hP
  simp only [N,Finset.card_range,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one]
  nlinarith [mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg r)]

#print axioms smooth_card_pow_le_moment
#print axioms smooth_card_pow_le_range_moment
end Waring.PolicyCompletionMomentLower
