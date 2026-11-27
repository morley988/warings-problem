import Waring.CartesianPolynomialBounds
import Waring.FiniteResourceHolder
import Waring.DiagonalCap

/-!
# Actual quadratic/coefficient factors under the resource Hölder allocation

The factor indexed by `none` is the completed quadratic sum. The factor
indexed by `some i` is the actual degree-sixteen/eighteen coefficient sum.
Their normalization caps are proved from the finite cardinalities. Resource
moment bounds have the exact finite-average meaning displayed here.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolynomialResourceBounds
open CoefficientFactorization CartesianPolynomialBounds FiniteResourceHolder

theorem norm_coefficientSum_le_card (p : ℕ) (C : Finset ℝ) (β : ℝ) :
    ‖coefficientSum p C β‖ ≤ (C.card:ℝ) := by
  unfold coefficientSum
  apply (norm_sum_le _ _).trans
  simp only [QuadraticModulation.norm_e, Finset.sum_const, nsmul_eq_mul, mul_one, le_refl]

theorem norm_quadraticSum_le_card (S : Finset ℤ) (β t : ℝ) :
    ‖quadraticSum S β t‖ ≤ (S.card:ℝ) := by
  unfold quadraticSum
  apply (norm_sum_le _ _).trans
  simp only [QuadraticModulation.norm_e, Finset.sum_const, nsmul_eq_mul, mul_one, le_refl]

def actualFactor {σ : Type*} {j : ℕ} (p : ℕ) (S : Finset ℤ)
    (C : Fin j → Finset ℝ) (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ) :
    Option (Fin j) → σ → ℝ
  | none, x => ‖quadraticSum S (β x) t‖
  | some i, x => ‖coefficientSum p (C i) (γ i x)‖

def normalizedFactor {σ : Type*} {j : ℕ} (p : ℕ) (S : Finset ℤ)
    (C : Fin j → Finset ℝ) (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ)
    (M : Option (Fin j) → ℝ) (i : Option (Fin j)) (x : σ) : ℝ :=
  actualFactor p S C β γ t i x/M i

theorem normalizedFactor_comp {σ τ : Type*} {j : ℕ} (p : ℕ) (S : Finset ℤ)
    (C : Fin j → Finset ℝ) (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ)
    (M : Option (Fin j) → ℝ) (g : τ → σ) (i : Option (Fin j)) (x : τ) :
    normalizedFactor p S C (fun y => β (g y)) (fun l y => γ l (g y)) t M i x =
      normalizedFactor p S C β γ t M i (g x) := by
  cases i <;> rfl

theorem actualFactor_nonneg {σ : Type*} {j : ℕ} (p : ℕ) (S : Finset ℤ)
    (C : Fin j → Finset ℝ) (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ)
    (i : Option (Fin j)) (x : σ) : 0 ≤ actualFactor p S C β γ t i x := by
  cases i <;> exact norm_nonneg _

theorem actualFactor_le_cap {σ : Type*} {j : ℕ} (p : ℕ) (S : Finset ℤ)
    (C : Fin j → Finset ℝ) (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ)
    (M : Option (Fin j) → ℝ) (hS : (S.card:ℝ) ≤ M none)
    (hC : ∀ i, ((C i).card:ℝ) ≤ M (some i)) (i : Option (Fin j)) (x : σ) :
    actualFactor p S C β γ t i x ≤ M i := by
  cases i with
  | none => exact (norm_quadraticSum_le_card S _ _).trans hS
  | some i => exact (norm_coefficientSum_le_card p (C i) _).trans (hC i)

theorem normalization_identity {σ : Type*} {j : ℕ} (p : ℕ) (S : Finset ℤ)
    (C : Fin j → Finset ℝ) (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ)
    (M : Option (Fin j) → ℝ) (hM : ∀ i, 0 < M i) (x : σ) :
    (∏ i, M i)*(∏ i, normalizedFactor p S C β γ t M i x) =
      ‖quadraticSum S (β x) t‖ * ∏ i, ‖coefficientSum p (C i) (γ i x)‖ := by
  rw [← Finset.prod_mul_distrib]
  calc
    _ = ∏ i, actualFactor p S C β γ t i x := by
      apply Finset.prod_congr rfl
      intro i hi
      exact mul_div_cancel₀ _ (hM i).ne'
    _ = _ := by simp only [Fintype.prod_option, actualFactor]

/-- The resource allocation applied to the actual completed product, with
all finite normalization constants restored. -/
theorem actual_product_resource_saving {σ ρ : Type*} {j : ℕ}
    [Fintype σ] [Nonempty σ] [Fintype ρ]
    (p : ℕ) (S : Finset ℤ) (C : Fin j → Finset ℝ)
    (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ)
    (M : Option (Fin j) → ℝ) (hM : ∀ i, 0 < M i)
    (hS : (S.card:ℝ) ≤ M none) (hC : ∀ i, ((C i).card:ℝ) ≤ M (some i))
    (factor : ρ → Option (Fin j)) (order weight : ρ → ℝ)
    (ho : ∀ r, 0 ≤ order r) (hw : ∀ r, 0 ≤ weight r)
    (hmass : ∑ r, weight r ≤ 1)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r=i), order r*weight r ≤ 1)
    (P : ℝ) (hP : 0 < P) (K saving : ρ → ℝ) (hK : ∀ r, 0 ≤ K r)
    (hresources : ∀ r, average (fun x =>
      (normalizedFactor p S C β γ t M (factor r) x)^(order r)) ≤ K r*P^(-saving r)) :
    (∑ x, ‖quadraticSum S (β x) t‖ * ∏ i, ‖coefficientSum p (C i) (γ i x)‖) ≤
      (Fintype.card σ:ℝ)*(∏ i, M i)*(∏ r, (K r)^(weight r))*P^(-(∑ r, weight r*saving r)) := by
  have H := sum_resource_saving (normalizedFactor p S C β γ t M) factor order weight
    (fun i x => div_nonneg (actualFactor_nonneg p S C β γ t i x) (hM i).le)
    (fun i x => (div_le_one (hM i)).mpr (actualFactor_le_cap p S C β γ t M hS hC i x))
    ho hw hmass hload P hP K saving hK hresources
  have Hmul := mul_le_mul_of_nonneg_left H
    (show 0 ≤ ∏ i, M i from Finset.prod_nonneg (fun i _ => (hM i).le))
  calc
    _ = (∏ i, M i)*(∑ x, ∏ i, normalizedFactor p S C β γ t M i x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      exact (normalization_identity p S C β γ t M hM x).symm
    _ ≤ _ := Hmul.trans_eq (by ring)

/-- Finset form, for the concrete h/ordinary-shift families used by the
polynomial bounds. Resources are literal averages on that finite family. -/
theorem finite_product_resource_saving {σ ρ : Type*} {j : ℕ} [Fintype ρ]
    (s : Finset σ) (hs : s.Nonempty)
    (p : ℕ) (S : Finset ℤ) (C : Fin j → Finset ℝ)
    (β : σ → ℝ) (γ : Fin j → σ → ℝ) (t : ℝ)
    (M : Option (Fin j) → ℝ) (hM : ∀ i, 0 < M i)
    (hS : (S.card:ℝ) ≤ M none) (hC : ∀ i, ((C i).card:ℝ) ≤ M (some i))
    (factor : ρ → Option (Fin j)) (order weight : ρ → ℝ)
    (ho : ∀ r, 0 ≤ order r) (hw : ∀ r, 0 ≤ weight r)
    (hmass : ∑ r, weight r ≤ 1)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r=i), order r*weight r ≤ 1)
    (P : ℝ) (hP : 0 < P) (K saving : ρ → ℝ) (hK : ∀ r, 0 ≤ K r)
    (hresources : ∀ r, average (fun x : s =>
      (normalizedFactor p S C β γ t M (factor r) x)^(order r)) ≤ K r*P^(-saving r)) :
    (∑ x ∈ s, ‖quadraticSum S (β x) t‖ * ∏ i, ‖coefficientSum p (C i) (γ i x)‖) ≤
      (s.card:ℝ)*(∏ i, M i)*(∏ r, (K r)^(weight r))*P^(-(∑ r, weight r*saving r)) := by
  classical
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have H := actual_product_resource_saving p S C (fun x : s => β x) (fun i x => γ i x) t
    M hM hS hC factor order weight ho hw hmass hload P hP K saving hK
    (by simpa only [normalizedFactor_comp] using hresources)
  have heq : (∑ x : s, ‖quadraticSum S (β x) t‖ * ∏ i, ‖coefficientSum p (C i) (γ i x)‖) =
      ∑ x ∈ s, ‖quadraticSum S (β x) t‖ * ∏ i, ‖coefficientSum p (C i) (γ i x)‖ := by
    exact Finset.sum_attach s (fun x => ‖quadraticSum S (β x) t‖ * ∏ i, ‖coefficientSum p (C i) (γ i x)‖)
  simpa only [Fintype.card_coe, heq] using H

#print axioms actual_product_resource_saving
#print axioms finite_product_resource_saving

end Waring.PolynomialResourceBounds
