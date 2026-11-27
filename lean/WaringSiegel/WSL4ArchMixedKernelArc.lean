import WaringSiegel.WSL4ArchProductMeasure
import WaringSiegel.WSL3PoissonMajorFourthProjection

/-! # Integration of the two genuine mixed-major kernels on one projected arc -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem mixedMajorKernel_single_arc_bound (δ : ℝ) (hδ : 0<δ) :
    ∃ C : ℝ, 0<C ∧ ∀ (D L V Z : ℝ), 0<D → 0≤V → 0≤Z → ∀ γ : K,
      ((traceConductor γ).absNorm:ℝ)≤L →
      ∀ f : ArchimedeanTraceTorus K → ℝ, Continuous f → (∀q,0≤f q) →
      (∀ θ ∈ productMajorArc (inverseDifferent K) D L γ,
        f (Submodule.Quotient.mk θ) ≤ V*
          (Z^4*((traceConductor γ).absNorm:ℝ)^(-(1/2):ℝ)*
            (productArcWeight D (θ-mixedEmbedding K γ))^(-(11/6):ℝ)+
            ((traceConductor γ).absNorm:ℝ)^((7/2):ℝ)*
            (productArcWeight D (θ-mixedEmbedding K γ))^((13/6):ℝ))) →
      (∫q in traceMajorArc D L γ,f q ∂traceHaar) ≤
        C*V*(D^finrank ℚ K)⁻¹ *
          (Z^4*((traceConductor γ).absNorm:ℝ)^(-(1/2):ℝ)+
            ((traceConductor γ).absNorm:ℝ)^((7/2):ℝ)*
              (L/((traceConductor γ).absNorm:ℝ))^((19/6:ℝ)+δ)) := by
  obtain ⟨CN,hCN,hn⟩ := productMajorArc_negative_weight_integral_bound (K:=K) (11/6) (by norm_num)
  obtain ⟨CP,hCP,hp⟩ := productMajorArc_positive_weight_integral_bound (K:=K) δ hδ
  let C := CN+CP
  have hC : 0<C := add_pos hCN hCP
  refine ⟨C,hC,fun D L V Z hD hV hZ γ hQL f hfc hfn hpoint => ?_⟩
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  let E := productMajorArc (inverseDifferent K) D L γ
  have hE : IsCompact E := productMajorArc_isCompact _ inverseDifferent_ne_zero _ _ hD γ
  let Q : ℝ := (traceConductor γ).absNorm
  have hQ : 0<Q := Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ)
  have hL0 : 0≤L := hQ.le.trans hQL
  let g0 : mixedSpace K → ℝ := fun θ => (productArcWeight D (θ-mixedEmbedding K γ))^(-(11/6):ℝ)
  let g1 : mixedSpace K → ℝ := fun θ => (productArcWeight D (θ-mixedEmbedding K γ))^((13/6):ℝ)
  have hgc (a : ℝ) : Continuous (fun θ : mixedSpace K =>
      (productArcWeight D (θ-mixedEmbedding K γ))^a) :=
    ((productArcWeight_continuous D).comp (continuous_id.sub continuous_const)).rpow_const
      (fun θ => Or.inl (productArcWeight_pos _ _).ne')
  have hgi0 : IntegrableOn g0 E μ := (hgc _).continuousOn.integrableOn_compact hE
  have hgi1 : IntegrableOn g1 E μ := (hgc _).continuousOn.integrableOn_compact hE
  have hi0 : (∫θ in E,g0 θ ∂μ) ≤ C*(D^finrank ℚ K)⁻¹ := by
    exact (hn D L hD γ).trans (mul_le_mul_of_nonneg_right (show CN≤C from le_add_of_nonneg_right hCP.le)
      (inv_nonneg.mpr (pow_nonneg hD.le _)))
  have hi1 : (∫θ in E,g1 θ ∂μ) ≤ C*(D^finrank ℚ K)⁻¹*(L/Q)^((19/6:ℝ)+δ) := by
    have hh := hp D L (13/6) hD (by norm_num) γ hQL
    rw [show (13/6:ℝ)+1+δ=(19/6:ℝ)+δ by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show CP≤C from le_add_of_nonneg_left hCN.le)
        (inv_nonneg.mpr (pow_nonneg hD.le _))) (Real.rpow_nonneg (by positivity) _))
  calc
    _ ≤ ∫θ in E,f (Submodule.Quotient.mk θ) ∂μ :=
      traceHaar_integral_projected_le E hE f hfc hfn
    _ ≤ ∫θ in E,V*(Z^4*Q^(-(1/2):ℝ)*g0 θ+Q^((7/2):ℝ)*g1 θ) ∂μ := by
      apply setIntegral_mono_on
        ((hfc.comp continuous_quotient_mk').continuousOn.integrableOn_compact hE)
        (((hgi0.const_mul _).add (hgi1.const_mul _)).const_mul V) hE.measurableSet
      exact hpoint
    _ = V*(Z^4*Q^(-(1/2):ℝ)*(∫θ in E,g0 θ ∂μ)+Q^((7/2):ℝ)*(∫θ in E,g1 θ ∂μ)) := by
      rw [integral_const_mul,integral_add (hgi0.const_mul _) (hgi1.const_mul _),
        integral_const_mul,integral_const_mul]
    _ ≤ V*(Z^4*Q^(-(1/2):ℝ)*(C*(D^finrank ℚ K)⁻¹)+
        Q^((7/2):ℝ)*(C*(D^finrank ℚ K)⁻¹*(L/Q)^((19/6:ℝ)+δ))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hi0 (by positivity))
        (mul_le_mul_of_nonneg_left hi1 (Real.rpow_nonneg hQ.le _))) hV
    _ = _ := by dsimp only [Q]; ring

#print axioms mixedMajorKernel_single_arc_bound
end WaringSiegel.WSL4
