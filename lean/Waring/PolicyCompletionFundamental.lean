import Waring.SeedCompletionFundamental
import Waring.SeedCompletionZeroBranch
import Waring.PolicyCompletionGoodRecurrence
import Waring.IntegerDifferenceDegree

/-!
# The complete fundamental and backward efficient-differencing recurrence

This is the composition of the proved exceptional-factor energy, proved
derivative-zero count, actual smooth block extraction and Holder reduction,
proved nonsingular congruence count, and the actual backward-difference
identity. The only size hypothesis is a polynomial bound on the derivative
values of the explicit integer polynomial. No source moment estimate or
efficient-differencing inequality is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionFundamental
open AuxiliaryL2Grouping PolicyCompletionHolder PolicyCompletionEndpointPartition
open PolicyCompletionGoodBranch PolicyCompletionGoodRecurrence
open SeedCompletionFundamental SeedCompletionZeroBranch
open SmoothMoments IntegerDifferencePolynomial

def sourceMixedMoment {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (Z : Finset ℤ) (Q R : ℝ) : ℝ :=
  mixedFrequencyEvenMoment (C ×ˢ Z)
    (polynomialValue (fun c => powerPolynomial k (params c))) 1
    (smoothNumbers Q R) (fun n => ((n^k : ℕ) : ℤ)) s

/-- A complete recurrence for the original mixed moment. It retains the
literal full next-stage moment, with all old and new parameters inside
one square. Both constants are uniform over all displayed domains. -/
theorem source_fundamental_backward {κ : Type*} [DecidableEq κ]
    (k : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cbad : ℝ, 0 < Cbad ∧ ∃ Cgood : ℝ, 0 < Cgood ∧
      ∀ (C : Finset κ) (params : κ → List (ℤ × ℤ)),
      (∀ c ∈ C, ∀ p ∈ params c, p.1 ≠ 0 ∧ p.2 ≠ 0) →
      (∀ c ∈ C, (params c).length < k) →
      ∀ (N : ℤ) (Z : Finset ℤ), Z ⊆ Finset.Icc 1 N →
      ∀ (P Q R M : ℝ), 1 ≤ Q → Q ≤ P → 1 ≤ M →
      (∀ a ∈ C ×ˢ Z,
        (derivativeMagnitude (fun c => powerPolynomial k (params c)) a : ℝ) ≤ P^B) →
      ∀ s : ℕ,
      sourceMixedMoment k (s+1) C params Z Q R ≤
        ((s : ℝ)+3) *
          (((C.card : ℝ)*((k-1 : ℕ) : ℝ))^2 * smoothMoment k (2*(s+1)) Q R +
          ((s : ℝ)+1)*(Cbad*M*Q*P^ε*sourceMixedMoment k s C params Z Q R) +
          Cgood*(C.card : ℝ)*Q^ε*((CoefficientPower.coefficientBlock Q R M).card : ℝ)^(2*(s+1)-1) *
            ((C.card : ℝ)*((CoefficientPower.coefficientBlock Q R M).card : ℝ)*(Z.card : ℝ)*
                smoothMoment k (2*(s+1)) (Q/M) R +
              2*Real.sqrt (nextSmoothMoment k (s+1) C params
                (CoefficientPower.coefficientBlock Q R M) N (Q/M) R *
                smoothMoment k (2*(s+1)) (Q/M) R))) := by
  classical
  obtain ⟨Cb,hCb,hfund⟩ := fundamental_energy_bound hB hε
  obtain ⟨Cg,hCg,hgood⟩ := goodSmooth_count_le_nextMoment (κ := κ) k hε
  refine ⟨Cb,hCb,Cg,hCg,?_⟩
  intro C params hparams hlength N Z hZ P Q R M hQ hQP hM hD s
  let F := fun c => powerPolynomial k (params c)
  have hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0 :=
    fun c hc p hp => (hparams c hc p hp).2
  have hdegree : ∀ c ∈ (C ×ˢ Z).image Prod.fst,
      0 < (F c).natDegree ∧ (F c).natDegree ≤ k := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    have hc := (Finset.mem_product.mp ha).1
    have hdeg := powerPolynomial_natDegree k (params a.1)
      (hparams a.1 hc) (hlength a.1 hc).le
    change 0 < (powerPolynomial k (params a.1)).natDegree ∧
      (powerPolynomial k (params a.1)).natDegree ≤ k
    rw [hdeg]
    exact ⟨Nat.sub_pos_of_lt (hlength a.1 hc),Nat.sub_le _ _⟩
  have hzero := polynomial_zero_energy_le (C ×ˢ Z) F k hdegree k (s+1) Q R
  have hcard : (((C ×ˢ Z).image Prod.fst).card : ℝ) ≤ (C.card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_product.mp ha).1
  have hzero' : ((collisionPairs (zeroSmoothEndpoints (s+1) (C ×ˢ Z) Q R
      (derivativeMagnitude F))
      (tupleFrequency (polynomialValue F) (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ) ≤
      ((C.card : ℝ)*((k-1 : ℕ) : ℝ))^2 * smoothMoment k (2*(s+1)) Q R := by
    apply hzero.trans
    gcongr
    exact smoothMoment_nonneg _ _ _ _
  have hg := hgood C params hm (s+1) (by omega) N Z hZ Q R M hQ hM
  have hf := hfund P Q R M hQ hQP hM (κ × ℤ) (C ×ˢ Z)
    (polynomialValue F) (derivativeMagnitude F) hD k s
  apply hf.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (add_le_add_right hzero' _) hg

#print axioms source_fundamental_backward
end Waring.PolicyCompletionFundamental
