import WaringSiegel.WSL3MomentOptimizedAll

/-!
# Actual outer-minor bounds for products and representation coefficients

The weights may differ from variable to variable. The common scale saving
follows from the actual optimized moment theorem for each fixed weight.
An elementary maximum comparison, product a_i <= sum a_i^p, suffices.
The target character has norm one, so its Fourier coefficient has the same
outer-minor saving, uniformly in the represented algebraic integer.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem nonnegative_product_le_sum_card_powers {p : ℕ} (hp : 0<p)
    (a : Fin p → ℝ) (ha : ∀ i, 0≤a i) :
    (∏ i, a i) ≤ ∑ i, a i^p := by
  have hne : (Finset.univ : Finset (Fin p)).Nonempty :=
    ⟨⟨0,hp⟩,Finset.mem_univ _⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ a hne
  calc
    _ ≤ ∏ _j : Fin p, a i := Finset.prod_le_prod (fun j _ => ha j) hmax
    _ = a i^p := by simp
    _ ≤ _ := Finset.single_le_sum (fun j _ => pow_nonneg (ha j) p) hi

theorem compactTraceWeylSum_product_minor_saving
    (k p : ℕ) (hk : 3≤k) (hp : 0<p)
    (hvariables : Thresholds.sufficientVariables k ≤ (p:ℤ))
    (f : Fin p → 𝓢(mixedSpace K, ℂ))
    (hc : ∀ i, HasCompactSupport (f i : mixedSpace K → ℂ)) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ∏ i : Fin p, ‖compactTraceWeylSum k (f i) (hc i) P (by linarith) q‖ ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  choose C η hC hη hbound using
    (fun i : Fin p => compactTraceWeylSum_optimized_minor_saving (f i) (hc i) k p hk hvariables)
  have hne : (Finset.univ : Finset (Fin p)).Nonempty :=
    ⟨⟨0,hp⟩,Finset.mem_univ _⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image Finset.univ η hne
  refine ⟨∑ j, C j,η i,?_,hη i,?_⟩
  · exact Finset.sum_pos' (fun j _ => (hC j).le) ⟨i,hi,hC i⟩
  intro P hP
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  let X : ℝ := P^finrank ℚ K
  have hX : 1≤X := one_le_pow₀ hP
  let F (j : Fin p) (q : ArchimedeanTraceTorus K) : ℝ :=
    ‖compactTraceWeylSum k (f j) (hc j) P hP0.ne' q‖
  have hF (j : Fin p) : Continuous (F j) :=
    (compactTraceWeylSum_continuous _ _ _ _ _).norm
  have hiF (j : Fin p) : Integrable (fun q => F j q^p) traceHaar :=
    ((hF j).pow p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiprod : Integrable (fun q => ∏ j, F j q) traceHaar :=
    (continuous_finset_prod _ (fun j _ => hF j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hisum : Integrable (fun q => ∑ j, F j q^p) traceHaar :=
    (continuous_finset_sum _ (fun j _ => (hF j).pow p)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hjbound (j : Fin p) :
      (∫ q in vinogradovMinorArcs (K := K) k P, F j q^p ∂traceHaar) ≤
        C j*X^((p:ℝ)-k-η i) := by
    apply (hbound j P hP).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by linarith [hmin j (Finset.mem_univ j)]))
      (hC j).le
  calc
    _ ≤ ∫ q in vinogradovMinorArcs (K := K) k P, ∑ j, F j q^p ∂traceHaar :=
      setIntegral_mono_on hiprod.integrableOn hisum.integrableOn
        (vinogradovMinorArcs_measurable _ _ hP0)
        (fun q _ => nonnegative_product_le_sum_card_powers hp (fun j => F j q)
          (fun _ => norm_nonneg _))
    _ = ∑ j, ∫ q in vinogradovMinorArcs (K := K) k P, F j q^p ∂traceHaar :=
      integral_finset_sum _ (fun j _ => (hiF j).integrableOn)
    _ ≤ ∑ j, C j*X^((p:ℝ)-k-η i) := Finset.sum_le_sum (fun j _ => hjbound j)
    _ = _ := by rw [Finset.sum_mul]

theorem compactTraceWeylSum_fourier_minor_saving
    (k p : ℕ) (hk : 3≤k) (hp : 0<p)
    (hvariables : Thresholds.sufficientVariables k ≤ (p:ℤ))
    (f : Fin p → 𝓢(mixedSpace K, ℂ))
    (hc : ∀ i, HasCompactSupport (f i : mixedSpace K → ℂ)) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P), ∀ target : 𝓞 K,
      ‖∫ q in vinogradovMinorArcs (K := K) k P,
        (∏ i : Fin p, compactTraceWeylSum k (f i) (hc i) P (by linarith) q) *
          traceTorusCharacter (-target) q ∂traceHaar‖ ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  obtain ⟨C,η,hC,hη,hbound⟩ := compactTraceWeylSum_product_minor_saving k p hk hp hvariables f hc
  refine ⟨C,η,hC,hη,?_⟩
  intro P hP target
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul,norm_prod,traceTorusCharacter,norm_latticeCharacter_eq_one,mul_one]
    using hbound P hP

#print axioms compactTraceWeylSum_product_minor_saving
#print axioms compactTraceWeylSum_fourier_minor_saving
end WaringSiegel.WSL3
