import Waring.SeedCompletionSmall
import Waring.SmoothBadEnergy
import Waring.DerivativeZeroCount
import Waring.PolicyCompletionGoodBranch
import Waring.PolicyCompletionEndpointPartition

/-!
# Fundamental efficient differencing from actual finite branch energies

Finite Cauchy over the branch labels bounds the complete collision count by
the sum of branch energies with a constant depending only on the tuple
length. The bad smooth set already includes small variables; its proved
energy bound therefore permits a direct zero/bad-coordinate/good cover.
-/

noncomputable section
open scoped BigOperators

namespace Waring.SeedCompletionFundamental
open AuxiliaryL2Grouping PolicyCompletionHolder PolicyCompletionGoodBlocks
open SmoothMoments SmoothBadEnergy SmoothBadFactorCount DerivativeZeroCount
open PolicyCompletionEndpointPartition

/-- A finite cover of the actual endpoint domain costs only the number of
cover labels in the second moment. Overlapping cover sets are permitted. -/
theorem collision_count_le_finite_cover {α κ : Type*}
    (A : Finset α) (I : Finset κ) (E : κ → Finset α) (f : α → ℤ)
    (hcover : ∀ a ∈ A, ∃ i ∈ I, a ∈ E i) :
    ((collisionPairs A f).card : ℝ) ≤
      (I.card : ℝ)*∑ i ∈ I, ((collisionPairs (E i) f).card : ℝ) := by
  classical
  let N := (A ∪ I.biUnion E).image f
  have hA : ∀ a ∈ A, f a ∈ N := by
    intro a ha
    exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ ha)
  have hE (i : κ) (hi : i ∈ I) : ∀ a ∈ E i, f a ∈ N := by
    intro a ha
    exact Finset.mem_image_of_mem _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i,hi,ha⟩))
  have hfull : ((collisionPairs A f).card : ℝ) =
      ∑ n ∈ N, ((A.filter (fun a => f a=n)).card : ℝ)^2 := by
    exact_mod_cast collision_card_eq_sum A f N hA
  have hbranch (i : κ) (hi : i ∈ I) : ((collisionPairs (E i) f).card : ℝ) =
      ∑ n ∈ N, (((E i).filter (fun a => f a=n)).card : ℝ)^2 := by
    exact_mod_cast collision_card_eq_sum (E i) f N (hE i hi)
  rw [hfull]
  calc
    _ ≤ ∑ n ∈ N, (I.card : ℝ)*∑ i ∈ I,
        (((E i).filter (fun a => f a=n)).card : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hsub : A.filter (fun a => f a=n) ⊆
          I.biUnion (fun i => (E i).filter (fun a => f a=n)) := by
        intro a ha
        rcases Finset.mem_filter.mp ha with ⟨ha,hfa⟩
        obtain ⟨i,hi,hai⟩ := hcover a ha
        exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hai,hfa⟩⟩
      have hcardN := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have hcardR : ((A.filter (fun a => f a=n)).card : ℝ) ≤
          ∑ i ∈ I, (((E i).filter (fun a => f a=n)).card : ℝ) := by
        exact_mod_cast hcardN
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ))
        (fun i => (((E i).filter (fun a => f a=n)).card : ℝ))
      simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
      exact (pow_le_pow_left₀ (by positivity) hcardR 2).trans hcs
    _ = (I.card : ℝ)*∑ i ∈ I, ∑ n ∈ N,
        (((E i).filter (fun a => f a=n)).card : ℝ)^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (hbranch i hi).symm

/-- The parent bad-factor estimate applied to an arbitrary remaining
smooth tuple, with its actual frequency retained. The restriction to nonzero
D-values is removed on the right by genuine collision-set inclusion. -/
theorem bad_remaining_energy_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q R M : ℝ), 1 ≤ Q → Q ≤ P → 1 ≤ M →
      ∀ (α : Type*) (A : Finset α) (f : α → ℤ) (D : α → ℕ),
      (∀ a ∈ A, (D a : ℝ) ≤ P^B) → ∀ k s : ℕ,
      ((collisionPairs
        (badEndpoints ((A.filter (fun a => D a ≠ 0)) ×ˢ finiteTuples (smoothNumbers Q R) s)
          Q R M (fun x => D x.1))
        (fun x => tupleFrequency f (fun _ n => ((n^k : ℕ) : ℤ)) x.1 +
          ((x.2^k : ℕ) : ℤ))).card : ℝ) ≤
        C*M*Q*P^ε*mixedFrequencyEvenMoment A f 1 (smoothNumbers Q R)
          (fun n => ((n^k : ℕ) : ℤ)) s := by
  classical
  obtain ⟨C,hC,hbound⟩ := bad_collision_count_le_rpow hB hε
  refine ⟨C,hC,?_⟩
  intro P Q R M hQ hQP hM α A f D hD k s
  have hP : 0 ≤ P := (zero_le_one.trans hQ).trans hQP
  let A₀ := A.filter (fun a => D a ≠ 0)
  let T := A₀ ×ˢ finiteTuples (smoothNumbers Q R) s
  let F := tupleFrequency f (fun _ : Fin s => fun n => ((n^k : ℕ) : ℤ))
  have hsize : ∀ x ∈ T, 0 < D x.1 ∧ (D x.1 : ℝ) ≤ P^B := by
    intro x hx
    have ha := Finset.mem_filter.mp (Finset.mem_product.mp hx).1
    exact ⟨Nat.pos_of_ne_zero ha.2,hD x.1 ha.1⟩
  have h := hbound P Q R M hQ hQP hM (α × (Fin s → ℕ)) T F (fun x => D x.1) hsize k
  have hE : ((collisionPairs T F).card : ℝ) ≤
      mixedFrequencyEvenMoment A f 1 (smoothNumbers Q R) (fun n => ((n^k : ℕ) : ℤ)) s := by
    have heq : ((collisionPairs T F).card : ℝ) =
        mixedFrequencyEvenMoment A₀ f 1 (smoothNumbers Q R)
          (fun n => ((n^k : ℕ) : ℤ)) s := by
      rw [mixedMoment_one_eq_tupleCollision]
      rfl
    rw [heq]
    exact mixedFrequencyEvenMoment_mono (Finset.filter_subset _ _)
      (Finset.Subset.refl _) f 1 (fun n => ((n^k : ℕ) : ℤ)) s
  exact h.trans (mul_le_mul_of_nonneg_left hE (by positivity))

/-- The complete smooth moment splits over the actual zero, marked-bad,
and all-good endpoint families, with only the fixed factor `s+2`. -/
theorem smooth_moment_le_branch_energies {α : Type*}
    (s : ℕ) (A : Finset α) (f : α → ℤ) (D : α → ℕ)
    (Q R M : ℝ) (g : ℕ → ℤ) :
    mixedFrequencyEvenMoment A f 1 (smoothNumbers Q R) g s ≤
      ((s : ℝ)+2) *
        (((collisionPairs (zeroSmoothEndpoints s A Q R D)
          (tupleFrequency f (fun _ => g))).card : ℝ) +
          (∑ i : Fin s, ((collisionPairs (markedBadEndpoints s A Q R M D i)
            (tupleFrequency f (fun _ => g))).card : ℝ)) +
          ((collisionPairs (goodSmoothEndpoints s A Q R M D)
            (tupleFrequency f (fun _ => g))).card : ℝ)) := by
  classical
  let E : Option (Option (Fin s)) → Finset (α × (Fin s → ℕ))
    | none => zeroSmoothEndpoints s A Q R D
    | some none => goodSmoothEndpoints s A Q R M D
    | some (some i) => markedBadEndpoints s A Q R M D i
  have hcover : ∀ x ∈ A ×ˢ finiteTuples (smoothNumbers Q R) s,
      ∃ i ∈ (Finset.univ : Finset (Option (Option (Fin s)))), x ∈ E i := by
    intro x hx
    rcases endpoint_cover s A Q R M D x hx with hz | hb | hg
    · exact ⟨none,Finset.mem_univ _,hz⟩
    · obtain ⟨i,hi⟩ := hb
      exact ⟨some (some i),Finset.mem_univ _,hi⟩
    · exact ⟨some none,Finset.mem_univ _,hg⟩
  have h := collision_count_le_finite_cover (A ×ˢ finiteTuples (smoothNumbers Q R) s)
    Finset.univ E (tupleFrequency f (fun _ => g)) hcover
  rw [mixedMoment_one_eq_tupleCollision]
  simp only [Finset.card_univ,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one,
    Fintype.sum_option,E] at h
  convert h using 1 <;> ring

/-- The genuine fundamental estimate, before any common-modulus or backward
step. The nonzero bad branch is discharged by its proved arithmetic energy
bound and the all-good family is the literal source solution family.
Small variables are included in the bad family through the factorization
`n=n*1`, so no short-set comparison hypothesis is necessary. -/
theorem fundamental_energy_bound {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q R M : ℝ), 1 ≤ Q → Q ≤ P → 1 ≤ M →
      ∀ (α : Type*) (A : Finset α) (f : α → ℤ) (D : α → ℕ),
      (∀ a ∈ A, (D a : ℝ) ≤ P^B) → ∀ k s : ℕ,
      mixedFrequencyEvenMoment A f 1 (smoothNumbers Q R)
        (fun n => ((n^k : ℕ) : ℤ)) (s+1) ≤
        ((s : ℝ)+3) *
          (((collisionPairs (zeroSmoothEndpoints (s+1) A Q R D)
            (tupleFrequency f (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ) +
          ((s : ℝ)+1)*(C*M*Q*P^ε*mixedFrequencyEvenMoment A f 1 (smoothNumbers Q R)
            (fun n => ((n^k : ℕ) : ℤ)) s) +
          ((collisionPairs (goodSmoothEndpoints (s+1) A Q R M D)
            (tupleFrequency f (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ)) := by
  classical
  obtain ⟨C,hC,hbad⟩ := bad_remaining_energy_le_rpow hB hε
  refine ⟨C,hC,?_⟩
  intro P Q R M hQ hQP hM α A f D hD k s
  have h := smooth_moment_le_branch_energies (s+1) A f D Q R M
    (fun n => ((n^k : ℕ) : ℤ))
  have hmarked (i : Fin (s+1)) :
      ((collisionPairs (markedBadEndpoints (s+1) A Q R M D i)
        (tupleFrequency f (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ) ≤
      C*M*Q*P^ε*mixedFrequencyEvenMoment A f 1 (smoothNumbers Q R)
        (fun n => ((n^k : ℕ) : ℤ)) s := by
    rw [markedBad_collision_card_eq i A Q R M D f (fun n => ((n^k : ℕ) : ℤ))]
    exact hbad P Q R M hQ hQP hM α A f D hD k s
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (s+1))))
    (fun i hi => hmarked i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,
    Nat.cast_one] at hsum
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_left hsum _) _) (by positivity))
  convert h' using 1 <;> congr 1 <;> push_cast <;> ring

#print axioms collision_count_le_finite_cover
#print axioms bad_remaining_energy_le_rpow
#print axioms smooth_moment_le_branch_energies
#print axioms fundamental_energy_bound

end Waring.SeedCompletionFundamental
