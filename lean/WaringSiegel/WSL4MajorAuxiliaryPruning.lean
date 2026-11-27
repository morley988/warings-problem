import WaringSiegel.WSL4MajorAuxiliaryCoefficient
import WaringSiegel.WSL4MajorAuxiliaryPhase
import WaringSiegel.WSL4MajorCubicPruning
import WaringSiegel.WSL4ArchAuxiliaryBroad

/-! # Broad-minus-narrow pruning for the literal auxiliary sources -/
noncomputable section
set_option maxHeartbeats 1300000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local WSL4Weil
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliaryTraceIntegrand_broad_pruning_bound
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (C0 : ℝ) (hC0 : 1≤C0) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 0<P) (p : ℕ) (hp : p.Prime), 6<p →
      ∀ L : ℝ, 0<L →
      (2:ℝ)^finrank ℚ K*(C0*P^finrank ℚ K)^2<
        (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*(P^3)^finrank ℚ K →
      ∀ target : 𝓞 K,
      (∫ q in traceMajorArcUnion (P^3) (C0*P^finrank ℚ K)\traceMajorArcUnion (P^3) L,
        ‖auxiliaryTraceIntegrand ρ R hρ hR P hP p hp.pos target q‖ ∂traceHaar) ≤
        C*(P^finrank ℚ K)^5*
          (1/L^((5:ℝ)/4)+((p:ℝ)^finrank ℚ K)^8/(P^finrank ℚ K)^((5:ℝ)/4)) := by
  obtain ⟨C,hC,hprune⟩ := traceMajorArcUnion_kappa_pruning_bound (K := K)
    cubicTwistExceptionalConstant cubicTwistExceptionalConstant_nonneg C0 hC0
  obtain ⟨D,hD,hpoint⟩ := auxiliary_root_four_by_four_broad_bound (K := K) ρ R hρ hR
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro P hP p hp hp6 L hL hsep target
  let X := P^finrank ℚ K
  let Y := (p:ℝ)^finrank ℚ K
  have hX : 0<X := pow_pos hP _
  have hY : 0≤Y := pow_nonneg (Nat.cast_nonneg _) _
  have hpw (γ : K) (β : mixedSpace K) :
      ‖auxiliaryTraceIntegrand ρ R hρ hR P hP p hp.pos target
          (Submodule.Quotient.mk (mixedEmbedding K γ+β))‖ ≤
        (D*X^8)*cubicKappaIdeal cubicTwistExceptionalConstant (traceConductor γ)^8*
          cubicPruningKernel ((traceConductor γ).absNorm:ℝ) X Y (P^3 • β) := by
    rw [auxiliaryTraceIntegrand_norm]
    have h := hpoint γ p hp hp6 P hP β
    rw [← cubicKappaIdeal_coe cubicTwistExceptionalConstant
      ⟨traceConductor γ,traceConductor_ne_zero γ⟩] at h
    apply h.trans_eq
    dsimp [cubicPruningKernel,X,Y]
    rw [← productArcWeight_scale_eq (P^3) (pow_nonneg hP.le _) β]
    ring
  have hh := hprune (P^3) X Y L (D*X^8) (pow_pos hP 3) hX hY hL
    (by positivity) hsep (auxiliaryTraceIntegrand ρ R hρ hR P hP p hp.pos target)
    (auxiliaryTraceIntegrand_continuous ρ R hρ hR P hP p hp.pos target) hpw
  have hvol : X^8*((P^3)^finrank ℚ K)⁻¹=X^5 := by
    simpa only [auxiliaryMajorScale,Nat.cast_one,one_pow,div_one] using
      auxiliary_major_volume_identity (K := K) P hP 1
  apply hh.trans_eq
  calc
    _ = C*D*(X^8*((P^3)^finrank ℚ K)⁻¹)*
        (1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) := by ring
    _ = _ := by rw [hvol]

theorem auxiliaryMajorCoefficient_sub_narrow_bound
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (C0 : ℝ) (hC0 : 1≤C0) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 0<P) (p : ℕ) (hp : p.Prime), 6<p →
      ∀ L : ℝ, 0<L → L≤C0*P^finrank ℚ K →
      (2:ℝ)^finrank ℚ K*(C0*P^finrank ℚ K)^2<
        (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*(P^3)^finrank ℚ K →
      ∀ target : 𝓞 K,
      ‖auxiliaryMajorCoefficient ρ R hρ hR P hP p hp.pos (C0*P^finrank ℚ K) target-
        auxiliaryMajorCoefficient ρ R hρ hR P hP p hp.pos L target‖ ≤
        C*(P^finrank ℚ K)^5*
          (1/L^((5:ℝ)/4)+((p:ℝ)^finrank ℚ K)^8/(P^finrank ℚ K)^((5:ℝ)/4)) := by
  obtain ⟨C,hC,hbound⟩ := auxiliaryTraceIntegrand_broad_pruning_bound (K := K) ρ R hρ hR C0 hC0
  refine ⟨C,hC,?_⟩
  intro P hP p hp hp6 L hL hLM hsep target
  exact (traceMajorArcUnion_integral_sub_norm_le_norm_integral (P^3) L (C0*P^finrank ℚ K)
    (pow_pos hP 3) hLM (auxiliaryTraceIntegrand ρ R hρ hR P hP p hp.pos target)
    (auxiliaryTraceIntegrand_continuous ρ R hρ hR P hP p hp.pos target)).trans
      (hbound P hP p hp hp6 L hL hsep target)

#print axioms auxiliaryTraceIntegrand_broad_pruning_bound
#print axioms auxiliaryMajorCoefficient_sub_narrow_bound
end WaringSiegel.WSL4
