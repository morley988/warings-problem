import Waring.PolicyCompletionGoodBranch
import Waring.SeedCompletionBackwardCount
import Waring.IntegerDifferencePolynomial

/-!
# Connecting the all-good branch to actual backward differencing

The common-modulus count is decomposed by its retained polynomial parameter.
At each parameter, the integer polynomial representation identifies its
frequency equation with the literal modifiedCenteredPower equation in the
backward-differencing step. No polynomial identity is left as a premise.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionBackward
open AuxiliaryL2Grouping PolicyCompletionGoodBranch PolicyCompletionCongruence
open SeedCompletionBackward SeedCompletionBackwardCount IntegerDifferencePolynomial

/-- The literal real-phase equation is exactly its integer polynomial
equation when the coefficients are nonzero. -/
theorem mem_stepSolutions_integer {ι : Type*} (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) (w : ℤ) (Z : Finset ℤ) (B : Finset ι) (U : ι → ℤ)
    (p : (ℤ × ι) × (ℤ × ι)) :
    p ∈ stepSolutions k (realParameters params) w Z B (fun u => (U u : ℝ)) ↔
      p ∈ ((Z ×ˢ B) ×ˢ (Z ×ˢ B)) ∧ w^k ∣ p.1.1-p.2.1 ∧
      (powerPolynomial k params).eval p.1.1+w^k*U p.1.2 =
        (powerPolynomial k params).eval p.2.1+w^k*U p.2.2 := by
  classical
  simp only [stepSolutions,Finset.mem_filter]
  rw [← powerPolynomial_eval_int k params hm p.1.1,
    ← powerPolynomial_eval_int k params hm p.2.1]
  constructor
  · rintro ⟨hdom,hdiv,heq⟩
    exact ⟨hdom,hdiv,by exact_mod_cast heq⟩
  · rintro ⟨hdom,hdiv,heq⟩
    exact ⟨hdom,hdiv,by exact_mod_cast heq⟩

/-- The common-modulus solutions have exactly one old polynomial parameter;
after retaining it, their count is the sum of the literal backward counts. -/
theorem commonModulus_card_eq_sum_steps {κ : Type*} [DecidableEq κ]
    (C : Finset κ) (Z : Finset ℤ) (B : Finset ℕ) (params : κ → List (ℤ × ℤ))
    (k s w : ℕ) (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) :
    (commonModulusSolutions (C ×ˢ Z) B (fun c => powerPolynomial k (params c)) s k w).card =
      ∑ c ∈ C, (stepSolutions k (realParameters (params c)) (w : ℤ) Z
        (finiteTuples B s) (fun u => (smoothTupleValue k s u : ℝ))).card := by
  classical
  let S := commonModulusSolutions (C ×ˢ Z) B (fun c => powerPolynomial k (params c)) s k w
  have hmem (p : ((κ × ℤ) × (Fin s → ℕ)) × ((κ × ℤ) × (Fin s → ℕ))) :
      p ∈ S ↔ p.1.1 ∈ C ×ˢ Z ∧ p.1.2 ∈ finiteTuples B s ∧
        p.2.1 ∈ C ×ˢ Z ∧ p.2.2 ∈ finiteTuples B s ∧
        (powerPolynomial k (params p.1.1.1)).eval p.1.1.2+(w : ℤ)^k*smoothTupleValue k s p.1.2 =
          (powerPolynomial k (params p.2.1.1)).eval p.2.1.2+(w : ℤ)^k*smoothTupleValue k s p.2.2 ∧
        p.1.1.1=p.2.1.1 ∧ p.1.1.2 % (w : ℤ)^k=p.2.1.2 % (w : ℤ)^k :=
    mem_sameClass_lifted _ _ _ _ _ _ _
  have hmap : S.toSet.MapsTo (fun p => p.1.1.1) C := by
    intro p hp
    exact (Finset.mem_product.mp (hmem p |>.mp hp).1).1
  change S.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.card_bij
    (fun p _ => ((p.1.1.2,p.1.2),(p.2.1.2,p.2.2)))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hc1⟩
    rcases (hmem p).mp hp with ⟨hA1,hB1,hA2,hB2,hfreq,hc12,hmod⟩
    have hc2 : p.2.1.1=c := hc12.symm.trans hc1
    rw [mem_stepSolutions_integer k (params c) (hm c hc)]
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hA1).2,hB1⟩,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp hA2).2,hB2⟩⟩,?_,?_⟩
    · exact Int.modEq_iff_dvd.mp hmod.symm
    · simpa only [hc1,hc2] using hfreq
  · intro p hp q hq heq
    have hp1 := (Finset.mem_filter.mp hp).2
    have hq1 := (Finset.mem_filter.mp hq).2
    have hp2 : p.2.1.1=c := ((hmem p).mp (Finset.mem_filter.mp hp).1).2.2.2.2.2.1.symm.trans hp1
    have hq2 : q.2.1.1=c := ((hmem q).mp (Finset.mem_filter.mp hq).1).2.2.2.2.2.1.symm.trans hq1
    have hzu : (p.1.1.2,p.1.2)=(q.1.1.2,q.1.2) :=
      congrArg (fun v : (ℤ × (Fin s → ℕ)) × (ℤ × (Fin s → ℕ)) => v.1) heq
    have hzv : (p.2.1.2,p.2.2)=(q.2.1.2,q.2.2) :=
      congrArg (fun v : (ℤ × (Fin s → ℕ)) × (ℤ × (Fin s → ℕ)) => v.2) heq
    have hzl := congrArg (fun v : ℤ × (Fin s → ℕ) => v.1) hzu
    have hul := congrArg (fun v : ℤ × (Fin s → ℕ) => v.2) hzu
    have hzr := congrArg (fun v : ℤ × (Fin s → ℕ) => v.1) hzv
    have hur := congrArg (fun v : ℤ × (Fin s → ℕ) => v.2) hzv
    exact Prod.ext
      (Prod.ext (Prod.ext (hp1.trans hq1.symm) hzl) hul)
      (Prod.ext (Prod.ext (hp2.trans hq2.symm) hzr) hur)
  · intro p hp
    rw [mem_stepSolutions_integer k (params c) (hm c hc)] at hp
    rcases hp with ⟨hdom,hdiv,hfreq⟩
    rcases Finset.mem_product.mp hdom with ⟨hleft,hright⟩
    rcases Finset.mem_product.mp hleft with ⟨hz,hu⟩
    rcases Finset.mem_product.mp hright with ⟨hz',hv⟩
    refine ⟨(((c,p.1.1),p.1.2),((c,p.2.1),p.2.2)),?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨(hmem _).mpr ⟨Finset.mem_product.mpr ⟨hc,hz⟩,hu,
      Finset.mem_product.mpr ⟨hc,hz'⟩,hv,hfreq,rfl,?_⟩,rfl⟩
    exact (Int.modEq_iff_dvd.mpr hdiv).symm

#print axioms mem_stepSolutions_integer
#print axioms commonModulus_card_eq_sum_steps

end Waring.PolicyCompletionBackward
