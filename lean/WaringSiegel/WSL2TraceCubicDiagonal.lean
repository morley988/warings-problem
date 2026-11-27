import WaringSiegel.WSL2TraceCubicMixed
import WaringSiegel.WSL2TraceMoments

/-!
# WSL2: the literal diagonal part of the cubic mixed moment

Haar preservation removes each nonzero multiplier m³ from the small-variable
fourth moment. The actual weighted diagonal energy therefore has the required
fourth-moment bound, uniformly in every multiplier set and every weight.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace WaringSiegel.WSL2

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]
variable {α β : Type*} [Fintype α] [Fintype β]

theorem traceWeylSum_mul_integral_norm_pow (a : 𝓞 K) (ha : a ≠ 0) (k n : ℕ)
    (nodes : β → 𝓞 K) (w : β → ℂ) :
    (∫ θ : ArchimedeanTraceTorus K, ‖traceWeylSum k nodes w (traceTorusMul a θ)‖^n ∂traceHaar) =
      ∫ θ : ArchimedeanTraceTorus K, ‖traceWeylSum k nodes w θ‖^n ∂traceHaar := by
  have h := integral_map (μ := traceHaar) (traceTorusMul_continuous a).measurable.aemeasurable
    ((traceWeylSum_continuous k nodes w).norm.pow n).aestronglyMeasurable
  rw [traceTorusMul_map_Haar a ha] at h
  exact h.symm

def traceCubicDiagonalEnergy (M : Finset (𝓞 K)) (w : α → ℂ)
    (small : β → 𝓞 K) (v : β → ℂ) (θ : ArchimedeanTraceTorus K) : ℝ :=
  ∑ m ∈ M, (∑ i : α, ‖w i‖^2) * ‖traceWeylSum 3 small v (traceTorusMul (m^3) θ)‖^4

theorem traceCubicDiagonalEnergy_integral (M : Finset (𝓞 K))
    (hM : ∀ m ∈ M, m ≠ 0) (w : α → ℂ) (small : β → 𝓞 K) (v : β → ℂ) :
    (∫ θ, traceCubicDiagonalEnergy M w small v θ ∂traceHaar) =
      (M.card:ℝ)*(∑ i : α, ‖w i‖^2) *
        ∫ θ : ArchimedeanTraceTorus K, ‖traceWeylSum 3 small v θ‖^4 ∂traceHaar := by
  have hi (m : 𝓞 K) : Integrable (fun θ : ArchimedeanTraceTorus K =>
      (∑ i : α, ‖w i‖^2) * ‖traceWeylSum 3 small v (traceTorusMul (m^3) θ)‖^4) traceHaar :=
    (continuous_const.mul (((traceWeylSum_continuous 3 small v).comp
      (traceTorusMul_continuous (m^3))).norm.pow 4)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∑ m ∈ M, ∫ θ : ArchimedeanTraceTorus K,
        (∑ i : α, ‖w i‖^2) * ‖traceWeylSum 3 small v (traceTorusMul (m^3) θ)‖^4 ∂traceHaar :=
      integral_finset_sum _ (fun m _ => hi m)
    _ = ∑ _m ∈ M, (∑ i : α, ‖w i‖^2) *
        ∫ θ : ArchimedeanTraceTorus K, ‖traceWeylSum 3 small v θ‖^4 ∂traceHaar := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_const_mul, traceWeylSum_mul_integral_norm_pow (m^3) (pow_ne_zero _ (hM m hm))]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A closed diagonal bound in the actual small-box volume scale. -/
theorem traceCubicDiagonalEnergy_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ {α β : Type*} [Fintype α] [Fintype β]
        (M : Finset (𝓞 K)), (∀ m ∈ M, m ≠ 0) →
      ∀ (w : α → ℂ) (small : β → 𝓞 K), Function.Injective small →
      (∀ j, ∀ z : InfinitePlace K, z (small j:K) ≤ R) →
      ∀ (v : β → ℂ) (V : ℝ), 0 ≤ V → (∀ j, ‖v j‖ ≤ V) →
      (∫ θ, traceCubicDiagonalEnergy M w small v θ ∂traceHaar) ≤
        C*(M.card:ℝ)*(∑ i : α, ‖w i‖^2)*(R^Module.finrank ℚ K : ℝ)^(2+ε)*V^4 := by
  obtain ⟨C, hC, hbound⟩ := numberField_fourth_moment_bound (K := K) 3 (by norm_num) hε
  refine ⟨C, hC, ?_⟩
  intro R hR α β _ _ M hM w small hinj hbox v V hV hv
  rw [traceCubicDiagonalEnergy_integral M hM w small v, traceWeylSum_integral_norm_pow]
  have hb := hbound R hR small hinj hbox v V hV hv
  have hm : 0 ≤ (M.card:ℝ)*(∑ i : α, ‖w i‖^2) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact (mul_le_mul_of_nonneg_left hb hm).trans_eq (by ring)

end WaringSiegel
