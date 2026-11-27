import WaringSiegel.WSL4ArchMixedPointwise

/-! # The two integrable major kernels for the literal mixed source -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem nearZeroMixedSIntegrand_major_bound
    (L : ℝ) (hL : 1≤L) (ε : ℝ) (hε : 0<ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0<B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0<C ∧ ∀ (H P M R : ℝ) (hH : 1≤H) (hP : 1≤P) (hM : 1≤M) (hR : 1≤R),
      H≤P → P≤H^2 → R^3=P^2*H → ∀ θ : mixedSpace K, ∀ γ : K,
      θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (L*P^finrank ℚ K) γ →
      ‖nearZeroMixedSIntegrand H P M R (by linarith) (by linarith) (by linarith) (by linarith)
          (Submodule.Quotient.mk θ)‖ ≤
        C*H^finrank ℚ K*P^finrank ℚ K*P^ε*M^finrank ℚ K*
          cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩^4 *
          ((R^finrank ℚ K)^4*((traceConductor γ).absNorm:ℝ)^(-(1/2):ℝ)*
            (productArcWeight (P^2*H) (θ-mixedEmbedding K γ))^(-(11/6):ℝ) +
            ((traceConductor γ).absNorm:ℝ)^((7/2):ℝ)*
            (productArcWeight (P^2*H) (θ-mixedEmbedding K γ))^((13/6):ℝ)) := by
  obtain ⟨CG,hCG,hg⟩ := nearZeroMixedSIntegrand_trivial_sixth (K:=K)
  obtain ⟨CF,hCF,hf⟩ := compactTraceQuadraticAbs_mixed_major_bound (K:=K)
    nearZeroSchwartz_majorant.1 nearZeroSchwartz_majorant.2.1
    nearZeroSchwartz_majorant.2.2.2.2.2 hε L hL
  obtain ⟨CU,hCU,hu⟩ := nearZeroTraceCubicSum_four_center_bound B hB hfinite
  refine ⟨8*CG*CF*CU^4,by positivity,fun H P M R hH hP hM hR hHP hPH hscale θ γ hmajor => ?_⟩
  have hH0 : 0<H := by linarith
  have hP0 : 0<P := by linarith
  have hM0 : 0<M := by linarith
  have hR0 : 0<R := by linarith
  let U : Finset (𝓞 K) := (compactIntegerSupport nearZeroSchwartz nearZeroSchwartz_majorant.2.1 H hH0.ne').erase 0
  let Q : ℝ := (traceConductor γ).absNorm
  let A := productArcWeight (P^2*H) (θ-mixedEmbedding K γ)
  let T := H^finrank ℚ K
  let X := P^finrank ℚ K
  let Y := M^finrank ℚ K
  let Z := R^finrank ℚ K
  let κ := cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩
  have hQ : 0<Q := Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ)
  have hA : 0<A := productArcWeight_pos _ _
  have hκ : 0≤κ := cubicKappa_nonneg B (fun v => (hB v).le) _
  have hT : 0≤T := pow_nonneg hH0.le _
  have hX : 0≤X := pow_nonneg hP0.le _
  have hY : 0≤Y := pow_nonneg hM0.le _
  have hZ : 0≤Z := pow_nonneg hR0.le _
  have hU0 : ∀ h∈U,h≠0 := fun h hh => (Finset.mem_erase.mp hh).1
  have hU : ∀ h∈U, ‖mixedEmbedding K (h:K)‖≤H := by
    intro h hh
    exact compactIntegerSupport_norm_bound nearZeroSchwartz_majorant.2.1
      nearZeroSchwartz_majorant.2.2.2.2.2 H hH0 (Finset.mem_erase.mp hh).2
  have hfb := hf P H hP hH hHP hPH θ γ hmajor U hU0 hU
  have hub := hu γ R hR0 (θ-mixedEmbedding K γ)
  have he : mixedEmbedding K γ+(θ-mixedEmbedding K γ)=θ := by abel
  rw [he,hscale] at hub
  change ‖nearZeroTraceCubicSum R hR0.ne' (traceTorusMul 4 (Submodule.Quotient.mk θ))‖ ≤
    CU*κ*(Z*A^(-(1/3):ℝ)+Q*A^((2/3):ℝ)) at hub
  have hbase := hg H P M R hH0.ne' hP0.ne' hM hR0.ne' (Submodule.Quotient.mk θ)
  have hnorm : ‖nearZeroMixedSIntegrand H P M R hH0.ne' hP0.ne' hM0.ne' hR0.ne'
      (Submodule.Quotient.mk θ)‖ ≤
      CG*Y*(CF*T*X*P^ε*(Q*A)^(-(1/2):ℝ)) *
        (CU*κ*(Z*A^(-(1/3):ℝ)+Q*A^((2/3):ℝ)))^4 := by
    apply hbase.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hfb (mul_nonneg hCG.le hY))
      (pow_le_pow_left₀ (norm_nonneg _) hub 4) (pow_nonneg (norm_nonneg _) 4) (by positivity)
  let D := CG*CF*CU^4*T*X*P^ε*Y*κ^4
  have hD : 0≤D := by dsimp [D]; positivity
  calc
    _ ≤ CG*Y*(CF*T*X*P^ε*(Q*A)^(-(1/2):ℝ)) *
        (CU*κ*(Z*A^(-(1/3):ℝ)+Q*A^((2/3):ℝ)))^4 := hnorm
    _ = D*((Q*A)^(-(1/2):ℝ)*(Z*A^(-(1/3):ℝ)+Q*A^((2/3):ℝ))^4) := by
      dsimp only [D]
      ring
    _ ≤ D*(8*(Z^4*Q^(-(1/2):ℝ)*A^(-(11/6):ℝ)+Q^((7/2):ℝ)*A^((13/6):ℝ))) :=
      mul_le_mul_of_nonneg_left (mixed_major_two_term_power Z Q A hZ hQ hA) hD
    _ = _ := by dsimp only [D,T,X,Y,Z,Q,A,κ]; ring

#print axioms nearZeroMixedSIntegrand_major_bound
end WaringSiegel.WSL4
