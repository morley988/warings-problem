import Waring.PolicyCompletionGoodBranch

/-!
# Adding an actual diagonal pair to the common-modulus equation

Every solution with s smooth variables on each side extends injectively
by any one element of the same short smooth set. The polynomial labels,
centers, frequency equation and congruence conditions are unchanged.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionDiagonalCounts
open PolicyCompletionGoodBranch PolicyCompletionCongruence
open AuxiliaryL2Grouping

/-- If the phase is injective in the center for every fixed parameter,
the zeroth smooth moment has at most one second center for each choice
of the two parameter labels and the first center. -/
theorem parameter_center_collision_card_le {κ ι : Type*}
    (C : Finset κ) (Z : Finset ι) (f : κ × ι → ℤ)
    (hinj : ∀ c ∈ C, Set.InjOn (fun z => f (c,z)) Z) :
    (collisionPairs (C ×ˢ Z) f).card ≤ C.card^2*Z.card := by
  classical
  let code (p : (κ × ι) × (κ × ι)) := ((p.1.1,p.2.1),p.1.2)
  have h := Finset.card_le_card_of_injOn code
    (s := collisionPairs (C ×ˢ Z) f) (t := (C ×ˢ C) ×ˢ Z)
  have hmap : ∀ p ∈ collisionPairs (C ×ˢ Z) f, code p ∈ (C ×ˢ C) ×ˢ Z := by
    intro p hp
    simp only [collisionPairs,Finset.mem_filter,Finset.mem_product] at hp
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨hp.1.1.1,hp.1.2.1⟩,hp.1.1.2⟩
  have hcode : Set.InjOn code (collisionPairs (C ×ˢ Z) f) := by
    rintro ⟨⟨c,z⟩,⟨d,w⟩⟩ hp ⟨⟨c',z'⟩,⟨d',w'⟩⟩ hq he
    simp only [code,Prod.mk.injEq] at he
    rcases he with ⟨⟨rfl,rfl⟩,rfl⟩
    change ((c,z),(d,w)) ∈ collisionPairs (C ×ˢ Z) f at hp
    change ((c,z),(d,w')) ∈ collisionPairs (C ×ˢ Z) f at hq
    simp only [collisionPairs,Finset.mem_filter,Finset.mem_product] at hp hq
    have hw := hinj d hp.1.2.1 hp.1.2.2 hq.1.2.2 (hp.2.symm.trans hq.2)
    subst w'
    rfl
  simpa only [Finset.card_product,pow_two] using h hmap hcode

/-- Every diagonal tuple contributes a genuine equal-sum solution. -/
theorem card_pow_le_frequencyEvenMoment {ι : Type*} (A : Finset ι)
    (f : ι → ℤ) (s : ℕ) :
    (A.card : ℝ)^s ≤ frequencyEvenMoment A f s := by
  classical
  rw [frequencyEvenMoment_eq_card]
  have h : (finiteTuples A s).card ≤ (equalSumPairs A f s).card := by
    apply Finset.card_le_card_of_injOn (fun u => (u,u))
    · intro u hu
      change (u,u) ∈ equalSumPairs A f s
      simp only [equalSumPairs,Finset.mem_filter,Finset.mem_product]
      exact ⟨⟨hu,hu⟩,True.intro⟩
    · intro u hu v hv huv
      exact congrArg Prod.fst huv
  simpa only [finiteTuples,Fintype.card_piFinset,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Nat.cast_pow] using (Nat.cast_le.mpr h :
      ((finiteTuples A s).card : ℝ) ≤ ((equalSumPairs A f s).card : ℝ))

def extendCollision {α β : Type*} {s : ℕ}
    (p : ((α × (Fin s → β)) × (α × (Fin s → β))) × β) :
      (α × (Fin (s+1) → β)) × (α × (Fin (s+1) → β)) :=
  ((p.1.1.1,Fin.cons p.2 p.1.1.2),(p.1.2.1,Fin.cons p.2 p.1.2.2))

theorem extendCollision_injective {α β : Type*} {s : ℕ} :
    Function.Injective (@extendCollision α β s) := by
  let decode (p : (α × (Fin (s+1) → β)) × (α × (Fin (s+1) → β))) :=
    (((p.1.1,Fin.tail p.1.2),(p.2.1,Fin.tail p.2.2)),p.1.2 0)
  have hleft : Function.LeftInverse decode extendCollision := by
    rintro ⟨⟨⟨a,u⟩,⟨b,v⟩⟩,n⟩
    simp [decode,extendCollision]
  exact hleft.injective

theorem mem_finiteTuples_cons {β : Type*} (B : Finset β) {s : ℕ}
    (b : β) (u : Fin s → β) :
    Fin.cons b u ∈ finiteTuples B (s+1) ↔ b ∈ B ∧ u ∈ finiteTuples B s := by
  simp [finiteTuples,Fintype.mem_piFinset,Fin.forall_fin_succ]

theorem smoothTupleValue_cons (k s : ℕ) (b : ℕ) (u : Fin s → ℕ) :
    smoothTupleValue k (s+1) (Fin.cons b u) = (b : ℤ)^k+smoothTupleValue k s u := by
  simp [smoothTupleValue,Fin.sum_univ_succ]

/-- Exact injective extension of a common-modulus solution by one
arbitrary diagonal short variable. -/
theorem commonModulus_card_mul_le {κ : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (B : Finset ℕ) (F : κ → Polynomial ℤ)
    (s k w : ℕ) :
    (commonModulusSolutions A B F s k w).card*B.card ≤
      (commonModulusSolutions A B F (s+1) k w).card := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn extendCollision
  · rintro ⟨⟨⟨a,u⟩,⟨b,v⟩⟩,n⟩ hp
    obtain ⟨hp,hn⟩ := Finset.mem_product.mp hp
    change _ ∈ sameClassCollisions _ _ _ at hp ⊢
    rw [mem_sameClass_lifted] at hp ⊢
    rcases hp with ⟨ha,hu,hb,hv,hfreq,hlabel,hresidue⟩
    refine ⟨ha,(mem_finiteTuples_cons B n u).mpr ⟨hn,hu⟩,
      hb,(mem_finiteTuples_cons B n v).mpr ⟨hn,hv⟩,?_,hlabel,hresidue⟩
    simp only [extendCollision,smoothTupleValue_cons]
    linear_combination hfreq
  · exact extendCollision_injective.injOn

/-- Summing over extracted factors retains the same diagonal multiplier. -/
theorem commonModulus_sum_mul_le {κ : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (B : Finset ℕ) (F : κ → Polynomial ℤ)
    (W : Finset ℕ) (s k : ℕ) :
    (B.card : ℝ)*(∑ w ∈ W,((commonModulusSolutions A B F s k w).card : ℝ)) ≤
      ∑ w ∈ W,((commonModulusSolutions A B F (s+1) k w).card : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have h := commonModulus_card_mul_le A B F s k w
  exact_mod_cast (by simpa only [Nat.mul_comm] using h)

#print axioms commonModulus_card_mul_le
#print axioms commonModulus_sum_mul_le
end Waring.SeedCompletionDiagonalCounts
