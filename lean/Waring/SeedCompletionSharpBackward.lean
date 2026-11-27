import Waring.PolicyCompletionFundamental
import Waring.SeedCompletionSmall

/-!
# The sharp backward step before terminal Holder

The complete next count is bounded by its actual cross integral
`integral |F_next| |f_scaled|^(2s)`. No Cauchy inequality is imposed before
selecting the terminal Holder weights. This is needed by the first A/B
seed updates; the earlier mixed-moment square-root bound remains valid.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Waring.SeedCompletionSharpBackward
open SeedCompletionBackward SeedCompletionBackwardCount SeedCompletionBackwardMoments
open SeedCompletionBackwardAggregate SeedCompletionSmall PolicyCompletionHolder
open PolicyCompletionBackward PolicyCompletionGoodBranch PolicyCompletionGoodRecurrence
open PolicyCompletionFundamental SeedCompletionFundamental SeedCompletionZeroBranch
open PolicyCompletionEndpointPartition AuxiliaryL2Grouping IntegerDifferencePolynomial
open SmoothMoments

/-- Exact Fourier product for two independently indexed families. -/
theorem frequencySum_product {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (x : ℝ) :
    frequencySum (A ×ˢ B) (fun p => f p.1+g p.2) x =
      frequencySum A f x * frequencySum B g x := by
  classical
  simp only [frequencySum,Finset.sum_product,fourier_add,
    Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

/-- The literal aggregate next cross integral, with all old and new labels
inside a single auxiliary sum and two unchanged tuple factors. -/
def aggregateNextCrossIntegral {κ ι : Type*} (k : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (w : κ → ℤ) (N : ℤ)
    (B : Finset ι) (U : ι → ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ‖frequencySum (aggregateNextDomain C w N k)
      (aggregateNextPhase k params w) x‖ *
    ‖frequencySum B (fun u => (2 : ℤ)^k*U u) x‖^2

theorem aggregateNextCrossIntegral_nonneg {κ ι : Type*} (k : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (w : κ → ℤ) (N : ℤ)
    (B : Finset ι) (U : ι → ℤ) :
    0 ≤ aggregateNextCrossIntegral k C params w N B U := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  positivity

/-- Orthogonality and the triangle inequality give the sharp cross integral.
The finite labels are aggregated before either operation. -/
theorem sum_next_step_count_le_crossIntegral {κ ι : Type*}
    (k : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ)) (w : κ → ℤ)
    (N : ℤ) (B : Finset ι) (U : ι → ℤ)
    (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) (hw : ∀ c ∈ C, w c ≠ 0) :
    (∑ c ∈ C, ((nextStepSolutions k (realParameters (params c)) (w c) N B
      (fun u => (U u : ℝ))).card : ℝ)) ≤
      aggregateNextCrossIntegral k C params w N B U := by
  have hcount : (∑ c ∈ C, ((nextStepSolutions k (realParameters (params c)) (w c) N B
      (fun u => (U u : ℝ))).card : ℝ)) =
      ((crossFrequencyPairs (aggregateNextDomain C w N k ×ˢ B) B
        (fun p => aggregateNextPhase k params w p.1+(2 : ℤ)^k*U p.2)
        (fun u => (2 : ℤ)^k*U u)).card : ℝ) := by
    exact_mod_cast sum_nextStepSolutions_card_eq_cross k C params w N B U hm hw
  rw [hcount]
  have h := cross_count_le_integral_norm (aggregateNextDomain C w N k ×ˢ B) B
    (fun p => aggregateNextPhase k params w p.1+(2 : ℤ)^k*U p.2)
    (fun u => (2 : ℤ)^k*U u)
  have hp (x : ℝ) :
      ‖frequencySum (aggregateNextDomain C w N k ×ˢ B)
        (fun p => aggregateNextPhase k params w p.1+(2 : ℤ)^k*U p.2) x‖ *
        ‖frequencySum B (fun u => (2 : ℤ)^k*U u) x‖ =
      ‖frequencySum (aggregateNextDomain C w N k) (aggregateNextPhase k params w) x‖ *
        ‖frequencySum B (fun u => (2 : ℤ)^k*U u) x‖^2 := by
    rw [frequencySum_product (aggregateNextDomain C w N k) B
      (aggregateNextPhase k params w) (fun u => (2 : ℤ)^k*U u) x,norm_mul]
    ring
  simpa only [hp] using h

/-- The complete backward inequality without premature mixed-moment Cauchy. -/
theorem sum_backward_count_le_crossIntegral {κ ι : Type*}
    (k : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ)) (w : κ → ℤ)
    (N : ℤ) (Z : κ → Finset ℤ) (B : Finset ι) (U : ι → ℤ)
    (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) (hw : ∀ c ∈ C, 0 < w c)
    (hZ : ∀ c ∈ C, Z c ⊆ Finset.Icc 1 N) :
    (∑ c ∈ C, ((stepSolutions k (realParameters (params c)) (w c) (Z c) B
      (fun u => (U u : ℝ))).card : ℝ)) ≤
      (∑ c ∈ C, ((Z c).card : ℝ))*secondMoment B U +
        2*aggregateNextCrossIntegral k C params w N B U := by
  have hsum : (∑ c ∈ C, ((stepSolutions k (realParameters (params c)) (w c) (Z c) B
      (fun u => (U u : ℝ))).card : ℝ)) ≤
      (∑ c ∈ C, ((Z c).card : ℝ))*secondMoment B U +
        2*∑ c ∈ C, ((nextStepSolutions k (realParameters (params c)) (w c) N B
          (fun u => (U u : ℝ))).card : ℝ) := by
    rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c hc
    have h := step_card_le_tuple_diagonal_add_next k (realParameters (params c))
      (w c) N (Z c) B (fun u => (U u : ℝ)) (hw c hc) (hZ c hc)
    rw [crossFrequencyPairs_intCast] at h
    rw [secondMoment_eq_count]
    exact_mod_cast h
  exact hsum.trans (add_le_add_left (mul_le_mul_of_nonneg_left
    (sum_next_step_count_le_crossIntegral k C params w N B U hm
      (fun c hc => (hw c hc).ne')) (by norm_num)) _)

/-- The actual smooth-tuple cross integral. -/
def nextSmoothCrossIntegral {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) : ℝ :=
  aggregateNextCrossIntegral k (C ×ˢ W) (fun p => params p.1) (fun p => (p.2 : ℤ)) N
    (finiteTuples (smoothNumbers Q R) s) (smoothTupleValue k s)

theorem nextSmoothCrossIntegral_nonneg {κ : Type*} (k s : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (W : Finset ℕ) (N : ℤ) (Q R : ℝ) :
    0 ≤ nextSmoothCrossIntegral k s C params W N Q R :=
  aggregateNextCrossIntegral_nonneg _ _ _ _ _ _ _

/-- The source common-modulus sum, retaining its sharp next cross integral. -/
theorem commonModulus_sum_le_crossIntegral {κ : Type*} [DecidableEq κ]
    (k s : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ))
    (W : Finset ℕ) (N : ℤ) (Z : Finset ℤ) (Q R : ℝ)
    (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0)
    (hw : ∀ w ∈ W, 0 < w) (hZ : Z ⊆ Finset.Icc 1 N) :
    (∑ w ∈ W,
      ((commonModulusSolutions (C ×ˢ Z) (smoothNumbers Q R)
        (fun c => powerPolynomial k (params c)) s k w).card : ℝ)) ≤
      (C.card : ℝ)*(W.card : ℝ)*(Z.card : ℝ)*smoothMoment k (2*s) Q R +
        2*nextSmoothCrossIntegral k s C params W N Q R := by
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
  have H := sum_backward_count_le_crossIntegral k (C ×ˢ W) (fun p => params p.1)
    (fun p => (p.2 : ℤ)) N (fun _ => Z) (finiteTuples (smoothNumbers Q R) s)
    (smoothTupleValue k s)
    (fun p hp => hm p.1 (Finset.mem_product.mp hp).1)
    (fun p hp => by
      change (0 : ℤ) < (p.2 : ℤ)
      exact_mod_cast hw p.2 (Finset.mem_product.mp hp).2)
    (fun _ _ => hZ)
  rw [tuple_secondMoment_eq_smoothMoment] at H
  simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_product,Nat.cast_mul,mul_assoc,
    nextSmoothCrossIntegral] using H

/-- The proved good branch, before selecting the terminal Holder weights. -/
theorem goodSmooth_count_le_crossIntegral {κ : Type*} [DecidableEq κ]
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (C : Finset κ) (params : κ → List (ℤ × ℤ)),
      (∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) →
      ∀ s : ℕ, 0 < s → ∀ (N : ℤ) (Z : Finset ℤ), Z ⊆ Finset.Icc 1 N →
      ∀ Q R M : ℝ, 1 ≤ Q → 1 ≤ M →
      ((goodSmoothSolutions (C ×ˢ Z) (fun c => powerPolynomial k (params c)) s k Q R M).card : ℝ) ≤
        K*(C.card : ℝ)*Q^ε*((CoefficientPower.coefficientBlock Q R M).card : ℝ)^(2*s-1) *
          ((C.card : ℝ)*((CoefficientPower.coefficientBlock Q R M).card : ℝ)*(Z.card : ℝ)*
              smoothMoment k (2*s) (Q/M) R +
            2*nextSmoothCrossIntegral k s C params (CoefficientPower.coefficientBlock Q R M)
              N (Q/M) R) := by
  obtain ⟨K,hK,hgood⟩ := goodSmooth_count_le_common_modulus (κ := κ) k k hε
  refine ⟨K,hK,?_⟩
  intro C params hm s hs N Z hZ Q R M hQ hM
  let W := CoefficientPower.coefficientBlock Q R M
  let J := smoothMoment k (2*s) (Q/M) R
  let T := (C.card : ℝ)*(W.card : ℝ)*(Z.card : ℝ)*J +
    2*nextSmoothCrossIntegral k s C params W N (Q/M) R
  have hdegree : ∀ c ∈ (C ×ˢ Z).image Prod.fst,
      (powerPolynomial k (params c)).natDegree ≤ k := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact (powerPolynomial_natDegree_le k (params x.1)
      (hm x.1 (Finset.mem_product.mp hx).1)).trans (Nat.sub_le _ _)
  have HG := hgood (C ×ˢ Z) (fun c => powerPolynomial k (params c)) hdegree s hs Q R M hQ hM
  have hWpos : ∀ w ∈ W, 0 < w := by
    intro w hw
    exact (mem_smoothNumbers.mp (Finset.mem_filter.mp hw).1).1.1
  have HT := commonModulus_sum_le_crossIntegral k s C params W N Z (Q/M) R hm hWpos hZ
  have hparams : (((C ×ˢ Z).image Prod.fst).card : ℝ) ≤ (C.card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_product.mp hx).1
  have hT0 : 0 ≤ T := by
    have hJ : 0 ≤ J := smoothMoment_nonneg _ _ _ _
    have hX := nextSmoothCrossIntegral_nonneg k s C params W N (Q/M) R
    dsimp only [T]
    positivity
  have hcoef : K*(((C ×ˢ Z).image Prod.fst).card : ℝ)*Q^ε*(W.card : ℝ)^(2*s-1) ≤
      K*(C.card : ℝ)*Q^ε*(W.card : ℝ)^(2*s-1) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hparams hK.le)
        (Real.rpow_nonneg (zero_le_one.trans hQ) ε)) (by positivity)
  apply HG.trans
  apply (mul_le_mul_of_nonneg_left HT (by positivity)).trans
  exact mul_le_mul_of_nonneg_right hcoef hT0

/-- The complete fundamental recurrence with the sharp source cross integral.
Every finite counting and Fourier step is proved; the displayed derivative
size condition is the actual integer polynomial bound. -/
theorem source_fundamental_sharp {κ : Type*} [DecidableEq κ]
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
              2*nextSmoothCrossIntegral k (s+1) C params
                (CoefficientPower.coefficientBlock Q R M) N (Q/M) R)) := by
  classical
  obtain ⟨Cb,hCb,hfund⟩ := fundamental_energy_bound hB hε
  obtain ⟨Cg,hCg,hgood⟩ := goodSmooth_count_le_crossIntegral (κ := κ) k hε
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

#print axioms sum_next_step_count_le_crossIntegral
#print axioms source_fundamental_sharp
end Waring.SeedCompletionSharpBackward
