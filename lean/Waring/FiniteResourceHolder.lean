import Waring.ResourceHolder
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Resource allocation on actual finite parameter averages

This is the finite real-valued interface to the proved integral resource
allocation. It uses the uniform counting probability measure, so both
unused Hölder mass and unused factor loads have exactly the certificate's
meaning. The result is an ordinary real inequality between finite sums.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Waring.FiniteResourceHolder

def average {σ : Type*} [Fintype σ] (f : σ → ℝ) : ℝ :=
  (∑ x, f x)/(Fintype.card σ:ℝ)

/-- Finite real resource allocation, with the exact sum of weighted savings. -/
theorem average_resource_saving {σ ι ρ : Type*}
    [Fintype σ] [Nonempty σ] [Fintype ι] [Fintype ρ] [DecidableEq ι]
    (f : ι → σ → ℝ) (factor : ρ → ι) (p w : ρ → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x) (hcap : ∀ i x, f i x ≤ 1)
    (hp : ∀ r, 0 ≤ p r) (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r=i), p r*w r ≤ 1)
    (P : ℝ) (hP : 0 < P) (C b : ρ → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hresources : ∀ r, average (fun x => (f (factor r) x)^(p r)) ≤ C r*P^(-b r)) :
    average (fun x => ∏ i, f i x) ≤ (∏ r, (C r)^(w r))*P^(-(∑ r, w r*b r)) := by
  classical
  letI : MeasurableSpace σ := ⊤
  haveI : MeasurableSingletonClass σ := ⟨fun _ => trivial⟩
  let μ : Measure σ := ((Fintype.card σ:ℝ≥0∞)⁻¹) • Measure.count
  have hcard : 0 < Fintype.card σ := Fintype.card_pos
  have hcardR : 0 < (Fintype.card σ:ℝ) := by exact_mod_cast hcard
  have hcardE : (Fintype.card σ:ℝ≥0∞) ≠ 0 := by exact_mod_cast hcard.ne'
  have hcount : (Measure.count : Measure σ) Set.univ = (Fintype.card σ:ℝ≥0∞) := by
    simp only [Measure.count_apply_finite Set.univ Set.finite_univ]
    simp
  haveI : IsProbabilityMeasure μ := ⟨by
    dsimp [μ]
    rw [hcount, ENNReal.inv_mul_cancel hcardE (by simp)]⟩
  have haverage (g : σ → ℝ) (hg : ∀ x, 0 ≤ g x) :
      (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ENNReal.ofReal (average g) := by
    dsimp [μ, average]
    rw [lintegral_smul_measure, lintegral_count, tsum_fintype, smul_eq_mul,
      ENNReal.ofReal_div_of_pos hcardR, ENNReal.ofReal_sum_of_nonneg (fun x _ => hg x)]
    simp only [ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  have H := ResourceHolder.probability_resource_saving (μ:=μ)
    (fun i x => ENNReal.ofReal (f i x)) factor p w
    (fun i => (measurable_of_countable _).aemeasurable)
    (fun i x => ENNReal.ofReal_le_one.mpr (hcap i x)) hp hw hmass hload
    (ENNReal.ofReal P) (by simpa using hP) (by simp)
    (fun r => ENNReal.ofReal (C r)) b (by
      intro r
      simp_rw [ENNReal.ofReal_rpow_of_nonneg (hf0 (factor r) _) (hp r)]
      rw [haverage _ (fun x => Real.rpow_nonneg (hf0 (factor r) x) _),
        ENNReal.ofReal_rpow_of_pos hP, ← ENNReal.ofReal_mul (hC r)]
      exact ENNReal.ofReal_le_ofReal (hresources r))
  have hprod (x : σ) : (∏ i, ENNReal.ofReal (f i x)) = ENNReal.ofReal (∏ i, f i x) :=
    (ENNReal.ofReal_prod_of_nonneg (fun i _ => hf0 i x)).symm
  simp_rw [hprod] at H
  rw [haverage _ (fun x => Finset.prod_nonneg (fun i _ => hf0 i x))] at H
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (hC _) (hw _)] at H
  rw [← ENNReal.ofReal_prod_of_nonneg (fun r _ => Real.rpow_nonneg (hC r) _),
    ENNReal.ofReal_rpow_of_pos hP,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun r _ => Real.rpow_nonneg (hC r) _))] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (Finset.prod_nonneg (fun r _ => Real.rpow_nonneg (hC r) _))
    (Real.rpow_nonneg hP.le _))).mp H

/-- Removing the finite average gives the actual finite product sum. -/
theorem sum_resource_saving {σ ι ρ : Type*}
    [Fintype σ] [Nonempty σ] [Fintype ι] [Fintype ρ] [DecidableEq ι]
    (f : ι → σ → ℝ) (factor : ρ → ι) (p w : ρ → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x) (hcap : ∀ i x, f i x ≤ 1)
    (hp : ∀ r, 0 ≤ p r) (hw : ∀ r, 0 ≤ w r)
    (hmass : ∑ r, w r ≤ 1)
    (hload : ∀ i, ∑ r ∈ Finset.univ.filter (fun r => factor r=i), p r*w r ≤ 1)
    (P : ℝ) (hP : 0 < P) (C b : ρ → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hresources : ∀ r, average (fun x => (f (factor r) x)^(p r)) ≤ C r*P^(-b r)) :
    (∑ x, ∏ i, f i x) ≤ (Fintype.card σ:ℝ)*(∏ r, (C r)^(w r))*P^(-(∑ r, w r*b r)) := by
  have H := average_resource_saving f factor p w hf0 hcap hp hw hmass hload P hP C b hC hresources
  have hc : 0 < (Fintype.card σ:ℝ) := by exact_mod_cast Fintype.card_pos (α:=σ)
  exact (div_le_iff₀ hc).mp H |>.trans_eq (by ring)

#print axioms average_resource_saving
#print axioms sum_resource_saving

end Waring.FiniteResourceHolder
