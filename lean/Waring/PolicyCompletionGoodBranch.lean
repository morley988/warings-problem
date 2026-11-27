import Waring.PolicyCompletionGoodBlocks
import Waring.PolicyCompletionNonsingular
import Mathlib.RingTheory.Int.Basic

/-!
# The complete all-good branch of the fundamental lemma

Smooth factor extraction, exact finite Cauchy/AM--GM, and the uniform
nonsingular polynomial root estimate are composed here on the original
finite solution count. The conclusion has the source factor
`P^epsilon * #parameters * #coefficientBlock^(2s-1)` times the sum of actual
common-modulus solution counts on the shorter smooth domain.

No efficient-differencing estimate or root estimate is a premise.
The exceptional small-variable, derivative-zero, and prime-supported cases
remain separate from this all-good branch.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionGoodBranch
open AuxiliaryL2Grouping PolicyCompletionHolder PolicyCompletionGoodBlocks
open PolicyCompletionCongruence SmoothMoments

def polynomialValue {κ : Type*} (F : κ → Polynomial ℤ) (x : κ × ℤ) : ℤ :=
  (F x.1).eval x.2

def derivativeMagnitude {κ : Type*} (F : κ → Polynomial ℤ) (x : κ × ℤ) : ℕ :=
  ((F x.1).derivative.eval x.2).natAbs

def smoothTupleValue (k s : ℕ) (u : Fin s → ℕ) : ℤ :=
  ∑ i, (u i : ℤ)^k

/-- The literal same-parameter common-modulus solutions on the chosen domain. -/
def commonModulusSolutions {κ : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (B : Finset ℕ) (F : κ → Polynomial ℤ)
    (s k w : ℕ) :=
  sameClassCollisions (A ×ˢ finiteTuples B s)
    (liftedFrequency (fun c z => (F c).eval z) (smoothTupleValue k s) ((w : ℤ)^k))
    (residueKey ((w : ℤ)^k))

/-- One homogeneous block is bounded by the actual common-modulus count.
The original parameter domain is retained after discarding the coprimality
restriction on the right through a genuine set inclusion. -/
theorem homogeneous_moment_le_common_modulus {κ : Type*} [DecidableEq κ]
    (d k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (κ × ℤ)) (F : κ → Polynomial ℤ),
      (∀ c ∈ A.image Prod.fst, (F c).natDegree ≤ d) →
      ∀ (B : Finset ℕ) (s w : ℕ), 0 < w →
      mixedFrequencyEvenMoment
        (singleBlockDomain A (fun q x => q.Coprime (derivativeMagnitude F x)) w)
        (polynomialValue F) 1 B (fun u => (w : ℤ)^k*(u : ℤ)^k) s ≤
      (C*((A.image Prod.fst).card : ℝ)*(w : ℝ)^ε) *
        ((commonModulusSolutions A B F s k w).card : ℝ) := by
  -- Reuse the uniform root constant across every tuple length. It comes from
  -- the degree/modulus estimate and is independent of the tuple type.
  obtain ⟨K,hK,hcapacity⟩ := nonsingular_residueCapacity_le (κ := κ) d k hε
  refine ⟨K,hK,?_⟩
  intro A F hdeg B s w hw
  let Ag := singleBlockDomain A (fun q x => q.Coprime (derivativeMagnitude F x)) w
  have hAg : Ag ⊆ A := by
    intro x hx
    simp only [Ag,singleBlockDomain,Finset.mem_filter] at hx
    exact hx.1
  have hparams : Ag.image Prod.fst ⊆ A.image Prod.fst := Finset.image_subset_image hAg
  have hdeg' : ∀ c ∈ Ag.image Prod.fst, (F c).natDegree ≤ d :=
    fun c hc => hdeg c (hparams hc)
  have hgood : ∀ x ∈ Ag, IsCoprime (w : ℤ) ((F x.1).derivative.eval x.2) := by
    intro x hx
    simp only [Ag,singleBlockDomain,Finset.mem_filter] at hx
    have hc := hx.2
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast,derivativeMagnitude] using hc
  have hcap := hcapacity Ag F hdeg' w hw hgood
  have hgroup := common_residue_collision_bound Ag (finiteTuples B s)
    (fun c z => (F c).eval z) (smoothTupleValue k s) ((w : ℤ)^k)
  have hpoints : Ag ×ˢ finiteTuples B s ⊆ A ×ˢ finiteTuples B s :=
    Finset.product_subset_product hAg (Finset.Subset.refl _)
  have hsol : sameClassCollisions (Ag ×ˢ finiteTuples B s)
      (liftedFrequency (fun c z => (F c).eval z) (smoothTupleValue k s) ((w : ℤ)^k))
      (residueKey ((w : ℤ)^k)) ⊆ commonModulusSolutions A B F s k w :=
    Finset.filter_subset_filter _ (Finset.filter_subset_filter _
      (Finset.product_subset_product hpoints hpoints))
  have hsolR : ((sameClassCollisions (Ag ×ˢ finiteTuples B s)
      (liftedFrequency (fun c z => (F c).eval z) (smoothTupleValue k s) ((w : ℤ)^k))
      (residueKey ((w : ℤ)^k))).card : ℝ) ≤
        ((commonModulusSolutions A B F s k w).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsol
  have hparamsR : ((Ag.image Prod.fst).card : ℝ) ≤ ((A.image Prod.fst).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hparams
  have hfreq : tupleFrequency (polynomialValue F)
      (fun _ : Fin s => fun u : ℕ => (w : ℤ)^k*(u : ℤ)^k) =
      liftedFrequency (fun c z => (F c).eval z) (smoothTupleValue k s) ((w : ℤ)^k) := by
    funext x
    simp only [tupleFrequency,polynomialValue,liftedFrequency,smoothTupleValue,Finset.mul_sum]
  rw [mixedMoment_one_eq_tupleCollision]
  change ((collisionPairs (Ag ×ˢ finiteTuples B s)
    (tupleFrequency (polynomialValue F) (fun _ => fun u => (w : ℤ)^k*(u : ℤ)^k))).card : ℝ) ≤ _
  rw [hfreq]
  apply hgroup.trans
  have hcapFull := hcap.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hparamsR hK.le) (Real.rpow_nonneg (by positivity) ε))
  exact mul_le_mul hcapFull hsolR (by positivity) (by positivity)

/-- The original all-good smooth equation, before extracting any factors. -/
def goodSmoothSolutions {κ : Type*} (A : Finset (κ × ℤ))
    (F : κ → Polynomial ℤ) (s k : ℕ) (P R M : ℝ) :=
  collisionPairs (goodSmoothEndpoints s A P R M (derivativeMagnitude F))
    (tupleFrequency (polynomialValue F) (fun _ n => ((n^k : ℕ) : ℤ)))

/-- The complete all-good branch, with the uniform small exponent loss and
the source coefficient-block exponent. Both sides count literal solutions. -/
theorem goodSmooth_count_le_common_modulus {κ : Type*} [DecidableEq κ]
    (d k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (κ × ℤ)) (F : κ → Polynomial ℤ),
      (∀ c ∈ A.image Prod.fst, (F c).natDegree ≤ d) →
      ∀ (s : ℕ), 0 < s → ∀ P R M : ℝ, 1 ≤ P → 1 ≤ M →
      ((goodSmoothSolutions A F s k P R M).card : ℝ) ≤
        C*((A.image Prod.fst).card : ℝ)*P^ε *
          ((CoefficientPower.coefficientBlock P R M).card : ℝ)^(2*s-1) *
          ∑ w ∈ CoefficientPower.coefficientBlock P R M,
            ((commonModulusSolutions A (smoothNumbers (P/M) R) F s k w).card : ℝ) := by
  obtain ⟨C,hC,hhom⟩ := homogeneous_moment_le_common_modulus (κ := κ) d k hε
  refine ⟨C,hC,?_⟩
  intro A F hdeg s hs P R M hP hM
  let W := CoefficientPower.coefficientBlock P R M
  let B := smoothNumbers (P/M) R
  let T : ℕ → ℝ := fun w => ((commonModulusSolutions A B F s k w).card : ℝ)
  have hG := goodSmooth_collisions_le_homogeneous (R := R) hs k A (polynomialValue F)
    (zero_le_one.trans hP) hM (derivativeMagnitude F)
  have hsum : (∑ w ∈ W,
      mixedFrequencyEvenMoment
        (singleBlockDomain A (fun q x => q.Coprime (derivativeMagnitude F x)) w)
        (polynomialValue F) 1 B (fun u => (w : ℤ)^k*(u : ℤ)^k) s) ≤
      (C*((A.image Prod.fst).card : ℝ)*P^ε) * ∑ w ∈ W, T w := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    have hwS : w ∈ smoothNumbers P R := (Finset.mem_filter.mp hw).1
    have hwpos : 0 < w := (mem_smoothNumbers.mp hwS).1.1
    have hwP : (w : ℝ) ≤ P :=
      (by exact_mod_cast (mem_smoothNumbers.mp hwS).1.2 : (w : ℝ) ≤ ⌊P⌋₊).trans
        (Nat.floor_le (zero_le_one.trans hP))
    apply (hhom A F hdeg B s w hwpos).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hwP hε.le)
        (by positivity)) (by positivity)
  calc
    _ ≤ (W.card : ℝ)^(2*s-1) * ∑ w ∈ W,
        mixedFrequencyEvenMoment
          (singleBlockDomain A (fun q x => q.Coprime (derivativeMagnitude F x)) w)
          (polynomialValue F) 1 B (fun u => (w : ℤ)^k*(u : ℤ)^k) s := hG
    _ ≤ (W.card : ℝ)^(2*s-1) *
        ((C*((A.image Prod.fst).card : ℝ)*P^ε) * ∑ w ∈ W, T w) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

#print axioms homogeneous_moment_le_common_modulus
#print axioms goodSmooth_count_le_common_modulus

end Waring.PolicyCompletionGoodBranch
