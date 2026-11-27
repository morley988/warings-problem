import Waring.CertificateAllocation

/-!
# Resource losses through the actual polynomial bounds

The analytic resource estimates are uniform bounds of the shape
`K * P ^ (epsilon - saving)`.  A finite allocation has total weight at most
one, so the combined exponent loses at most epsilon, independently of the
number of selected resources.  The diagonal cap is 1-Lipschitz in this loss,
and the actual one- and two-difference polynomial estimates divide the loss
by two and four respectively.

These are composition lemmas for actual finite averages and actual sums.
They retain the analytic resource-moment premises.  They do not assert
`AnalyticPolicySound`, efficient differencing, or a source moment estimate.
-/

noncomputable section
open scoped BigOperators

namespace Waring.ResourceDifferencingCap
open PolynomialSumReduction CartesianPolynomialBounds PolynomialResourceBounds
open CoefficientFactorization FiniteResourceHolder UnseparatedDifferencing Differences

/-- Allocate the same arbitrary small exponent loss to every selected resource.
The weights, orders, constants, and feasibility witnesses remain unchanged. -/
def Allocation.withLoss {j ρ} [Fintype ρ] (R : Allocation j ρ) (δ : ℝ) :
    Allocation j ρ :=
  { R with saving := fun r => R.saving r - δ }

@[simp] theorem Allocation.withLoss_totalConstant {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (δ : ℝ) :
    (R.withLoss δ).totalConstant = R.totalConstant := rfl

@[simp] theorem Allocation.withLoss_effectiveConstant {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (δ : ℝ) (N : ℕ) :
    (R.withLoss δ).effectiveConstant N = R.effectiveConstant N := rfl

theorem Allocation.withLoss_totalSaving {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (δ : ℝ) :
    (R.withLoss δ).totalSaving = R.totalSaving - δ * ∑ r, R.weight r := by
  simp only [Allocation.totalSaving, Allocation.withLoss, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Unused Hölder mass cannot increase the exponent loss. -/
theorem Allocation.withLoss_totalSaving_ge {j ρ} [Fintype ρ]
    (R : Allocation j ρ) {δ : ℝ} (hδ : 0 ≤ δ) :
    R.totalSaving - δ ≤ (R.withLoss δ).totalSaving := by
  rw [R.withLoss_totalSaving]
  have h := mul_le_mul_of_nonneg_left R.mass_le hδ
  linarith

/-- The retained minimum with one is Lipschitz with constant one. -/
theorem Allocation.withLoss_cap_ge {j ρ} [Fintype ρ]
    (R : Allocation j ρ) {δ : ℝ} (hδ : 0 ≤ δ) :
    min 1 R.totalSaving - δ ≤ min 1 (R.withLoss δ).totalSaving := by
  apply le_min
  · have h := min_le_left (1 : ℝ) R.totalSaving
    linarith
  · exact (sub_le_sub_right (min_le_right (1 : ℝ) R.totalSaving) δ).trans
      (R.withLoss_totalSaving_ge hδ)

/-- Exact conversion of resource estimates with epsilon loss into the finite
allocation interface; no constant is permitted to depend on the sample. -/
theorem Allocation.hasMoments_withLoss {j ρ σ} [Fintype ρ] [Fintype σ]
    (R : Allocation j ρ) (P δ : ℝ) (f : Option (Fin j) → σ → ℝ)
    (hmom : ∀ r, average (fun x => (f (R.factor r) x) ^ (R.order r)) ≤
      R.constant r * P ^ (δ - R.saving r)) :
    (R.withLoss δ).HasMoments P f := by
  intro r
  simpa only [Allocation.withLoss, neg_sub] using hmom r

/-- The root step attenuates the loss by the exact root exponent. -/
theorem Allocation.withLoss_cap_power {j ρ} [Fintype ρ]
    (R : Allocation j ρ) {P δ d : ℝ} (hP : 1 ≤ P) (hδ : 0 ≤ δ) (hd : 0 < d) :
    P ^ (-min 1 (R.withLoss δ).totalSaving / d) ≤
      P ^ (δ / d - min 1 R.totalSaving / d) := by
  apply Real.rpow_le_rpow_of_exponent_le hP
  have hcap := R.withLoss_cap_ge hδ
  calc
    -min 1 (R.withLoss δ).totalSaving / d ≤ (δ - min 1 R.totalSaving) / d :=
      div_le_div_of_nonneg_right (by linarith) hd.le
    _ = δ / d - min 1 R.totalSaving / d := sub_div _ _ _

/-- A real finite-average Hölder estimate with one common epsilon loss. -/
theorem Allocation.average_withLoss {j ρ σ} [Fintype ρ] [Fintype σ] [Nonempty σ]
    (R : Allocation j ρ) (f : Option (Fin j) → σ → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x) (hcap : ∀ i x, f i x ≤ 1)
    {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 ≤ δ)
    (hmom : ∀ r, average (fun x => (f (R.factor r) x) ^ (R.order r)) ≤
      R.constant r * P ^ (δ - R.saving r)) :
    average (fun x => ∏ i, f i x) ≤ R.totalConstant * P ^ (δ - R.totalSaving) := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have H := average_resource_saving f (R.withLoss δ).factor
    (R.withLoss δ).order (R.withLoss δ).weight hf0 hcap
    (R.withLoss δ).order_nonneg (R.withLoss δ).weight_nonneg
    (R.withLoss δ).mass_le (R.withLoss δ).load_le P hPp
    (R.withLoss δ).constant (R.withLoss δ).saving (R.withLoss δ).constant_nonneg
    (R.hasMoments_withLoss P δ f hmom)
  change average (fun x => ∏ i, f i x) ≤
    R.totalConstant * P ^ (-(R.withLoss δ).totalSaving) at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ R.totalConstant_nonneg
  apply Real.rpow_le_rpow_of_exponent_le hP
  have h := R.withLoss_totalSaving_ge hδ
  linarith

/-- The original one-difference polynomial estimate with the actual uniform
resource losses retained explicitly. -/
theorem first_polynomial_resource_cap_with_loss {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (k p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card : ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hred : ∀ h m : Fin j → ℝ, (∀ l, m l ≠ 0) → ∀ u z : ℝ,
      ordinaryDifference (modifiedCenteredPower k (parameters h m)) u z =
        normalForm p A ((∏ l, h l) * u) (u ^ 2) h m (2 * z + u))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmom : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r,
      average (fun x : H ×ˢ Finset.Icc (1 : ℤ) (N : ℤ) =>
        (firstFactors p A α C N V t (R.factor r) x) ^ (R.order r)) ≤
          R.constant r * (N : ℝ) ^ (δ - R.saving r)) :
    ‖polynomialFamily k (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (2 * (1 + 2 * R.effectiveConstant N)) ^ ((2 : ℝ)⁻¹) *
        ((N : ℝ) * parameterScale H V) *
          (N : ℝ) ^ (δ / 2 - min 1 R.totalSaving / 2) := by
  have HG := first_polynomial_resource_cap (R.withLoss δ) k p A α H hH C N Q hN hQN
    V hV hC hm hred (fun t ht => R.hasMoments_withLoss (N : ℝ) δ _ (hmom t ht))
  rw [R.withLoss_effectiveConstant] at HG
  apply HG.trans
  apply mul_le_mul_of_nonneg_left
    (R.withLoss_cap_power (by exact_mod_cast hN) hδ (by norm_num : (0 : ℝ) < 2))
  have hK := R.effectiveConstant_nonneg N hN
  exact mul_nonneg
    (Real.rpow_nonneg (by positivity) _)
    (mul_nonneg (by positivity) (parameterScale_nonneg H V (fun i => (hV i).le)))

/-- The original two-difference polynomial estimate with the same actual
resource hypotheses; the final exponent loses at most delta/4. -/
theorem second_polynomial_resource_cap_with_loss {j ρ} [Fintype ρ]
    (R : Allocation j ρ) (k p : ℕ) (A α : ℝ) (H : Finset (Fin j → ℝ))
    (hH : H.Nonempty) (C : Fin j → Finset ℝ) (N Q : ℕ) (hN : 0 < N) (hQN : Q ≤ N)
    (V : Fin j → ℝ) (hV : ∀ i, 0 < V i) (hC : ∀ i, ((C i).card : ℝ) ≤ V i)
    (hm : ∀ i, ∀ m ∈ C i, m ≠ 0)
    (hred : ∀ h m : Fin j → ℝ, (∀ l, m l ≠ 0) → ∀ u v z : ℝ,
      ordinaryDifference (ordinaryDifference (modifiedCenteredPower k (parameters h m)) u) v z =
        normalForm p A ((∏ l, h l) * u * v) (u ^ 2 + v ^ 2) h m (2 * z + u + v))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hmom : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r,
      average (fun x : (H ×ˢ Finset.Icc (1 : ℤ) (N : ℤ)) ×ˢ Finset.Icc (1 : ℤ) (N : ℤ) =>
        (secondFactors p A α C N V t (R.factor r) x) ^ (R.order r)) ≤
          R.constant r * (N : ℝ) ^ (δ - R.saving r)) :
    ‖polynomialFamily k (cartesianParameters H C) Prod.fst Prod.snd α 1 Q‖ ≤
      (32 * (1 + R.effectiveConstant N)) ^ ((4 : ℝ)⁻¹) *
        ((N : ℝ) * parameterScale H V) *
          (N : ℝ) ^ (δ / 4 - min 1 R.totalSaving / 4) := by
  have HG := second_polynomial_resource_cap (R.withLoss δ) k p A α H hH C N Q hN hQN
    V hV hC hm hred (fun t ht => R.hasMoments_withLoss (N : ℝ) δ _ (hmom t ht))
  rw [R.withLoss_effectiveConstant] at HG
  apply HG.trans
  apply mul_le_mul_of_nonneg_left
    (R.withLoss_cap_power (by exact_mod_cast hN) hδ (by norm_num : (0 : ℝ) < 4))
  have hK := R.effectiveConstant_nonneg N hN
  exact mul_nonneg
    (Real.rpow_nonneg (by positivity) _)
    (mul_nonneg (by positivity) (parameterScale_nonneg H V (fun i => (hV i).le)))

#print axioms Allocation.average_withLoss
#print axioms first_polynomial_resource_cap_with_loss
#print axioms second_polynomial_resource_cap_with_loss

end Waring.ResourceDifferencingCap

namespace Waring.Certificate
open ResourceDifferencingCap FiniteResourceHolder

/-- The finite certificate's literal saving survives actual resource losses.
All constants are finite real numbers; the conclusion is an actual average. -/
theorem piece_average_with_loss {σ : Type*} [Fintype σ] [Nonempty σ]
    (k : ℕ) (p : Policy) (coefficient : Curve) (piece : Piece) (height : ℝ)
    (hv : PieceAllocationValid p.phi.size piece)
    (K : Fin piece.resources.size → ℝ) (hK : ∀ r, 0 ≤ K r)
    (f : Option (Fin p.phi.size) → σ → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x) (hcap : ∀ i x, f i x ≤ 1)
    {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 ≤ δ)
    (hmom : ∀ r,
      average (fun x =>
        (f (allocationFactor p.phi.size (resourceAt piece r).factor (hv.1 r).2) x) ^
          ((resourceAt piece r).order : ℝ)) ≤
        K r * P ^ (δ - resourceReal k p coefficient (resourceAt piece r) height)) :
    average (fun x => ∏ i, f i x) ≤
      (∏ r, (K r) ^ ((resourceAt piece r).weight : ℝ)) *
        P ^ (δ - pieceSavingReal k p coefficient piece height) := by
  let R := pieceAllocation k p coefficient piece height hv K hK
  have H := R.average_withLoss f hf0 hcap hP hδ hmom
  rw [pieceAllocation_totalSaving] at H
  exact H

#print axioms piece_average_with_loss

end Waring.Certificate
