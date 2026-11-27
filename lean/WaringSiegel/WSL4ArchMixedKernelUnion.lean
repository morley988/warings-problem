import WaringSiegel.WSL4ArchMixedKernelArc
import WaringSiegel.WSL4ArchCenterMass

/-! # Actual finite-union integration of the mixed major kernels and conductor masses -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem mixed_major_kernel_conductor_identity (Q L δ : ℝ) (hQ : 0<Q) (hL : 0≤L) :
    Q^((7/2):ℝ)*(L/Q)^((19/6:ℝ)+δ) =
      L^((19/6:ℝ)+δ)*Q^((1/3:ℝ)-δ) := by
  rw [Real.div_rpow hL hQ.le]
  calc
    _ = L^((19/6:ℝ)+δ)*(Q^((7/2):ℝ)/Q^((19/6:ℝ)+δ)) := by ring
    _ = L^((19/6:ℝ)+δ)*Q^((7/2:ℝ)-((19/6:ℝ)+δ)) := by rw [Real.rpow_sub hQ]
    _ = _ := by congr 2 <;> ring

theorem mixedMajorKernel_union_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0≤B v)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ C : ℝ, 0<C ∧ ∀ (D L V Z : ℝ), 0<D → 1≤L → 0≤V → 0≤Z →
      ∀ f : ArchimedeanTraceTorus K → ℝ, Continuous f → (∀q,0≤f q) →
      (∀ (γ : K) (θ : mixedSpace K), θ ∈ productMajorArc (inverseDifferent K) D L γ →
        f (Submodule.Quotient.mk θ) ≤ V*cubicKappaIdeal B (traceConductor γ)^4 *
          (Z^4*((traceConductor γ).absNorm:ℝ)^(-(1/2):ℝ)*
            (productArcWeight D (θ-mixedEmbedding K γ))^(-(11/6):ℝ)+
            ((traceConductor γ).absNorm:ℝ)^((7/2):ℝ)*
            (productArcWeight D (θ-mixedEmbedding K γ))^((13/6):ℝ))) →
      (∫q in traceMajorArcUnion (K:=K) D L,f q ∂traceHaar) ≤
        C*V*(D^finrank ℚ K)⁻¹*(Z^4+L^((7/2:ℝ)+2*δ)) := by
  obtain ⟨CK,hCK,hk⟩ := mixedMajorKernel_single_arc_bound (K:=K) δ hδ
  obtain ⟨CN,hCN,hn⟩ := traceRationalCenters_kappa_negative_half_bound B hB
  obtain ⟨CT,hCT,ht⟩ := traceRationalCenters_kappa_truncated_bound B hB (2*δ) (by positivity)
  refine ⟨CK*(CN+CT),by positivity,fun D L V Z hD hL hV hZ f hfc hfn hpoint => ?_⟩
  have hL0 : 0<L := by linarith
  let N := ⌊L⌋₊
  letI := Fintype.ofFinite (traceRationalCenters K N)
  let Q : traceRationalCenters K N → ℝ := fun q => (traceConductor (traceCenterRepresentative q)).absNorm
  let κ : traceRationalCenters K N → ℝ := fun q => cubicKappaIdeal B (traceConductor (traceCenterRepresentative q))
  have hQ (q : traceRationalCenters K N) : 0<Q q :=
    Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero _)
  have hQL (q : traceRationalCenters K N) : Q q≤L := by
    have hh : Q q≤(N:ℝ) := by
      dsimp only [Q]
      exact_mod_cast (traceCenterRepresentative_spec q).2
    exact hh.trans (Nat.floor_le hL0.le)
  have hκ (q : traceRationalCenters K N) : 0≤κ q := cubicKappaIdeal_nonneg B hB _
  have hs0 : (∑q,Q q^(-(1/2):ℝ)*κ q^4)≤CN := hn N
  have hs1 : (∑q,Q q^((1/3:ℝ)-δ)*κ q^4)≤CT*L^((1/3:ℝ)+δ) := by
    have hh := ht ((1/3:ℝ)-δ) (by linarith) L hL
    rw [show (1/3:ℝ)-δ+2*δ=(1/3:ℝ)+δ by ring] at hh
    exact hh
  have hmass :
      (∑q : traceRationalCenters K N, CK*(V*κ q^4)*(D^finrank ℚ K)⁻¹ *
        (Z^4*Q q^(-(1/2):ℝ)+Q q^((7/2):ℝ)*(L/Q q)^((19/6:ℝ)+δ))) =
      CK*V*(D^finrank ℚ K)⁻¹ *
        (Z^4*(∑q,Q q^(-(1/2):ℝ)*κ q^4)+
          L^((19/6:ℝ)+δ)*(∑q,Q q^((1/3:ℝ)-δ)*κ q^4)) := by
    calc
      _ = ∑q : traceRationalCenters K N, CK*V*(D^finrank ℚ K)⁻¹ *
          (Z^4*(Q q^(-(1/2):ℝ)*κ q^4)+L^((19/6:ℝ)+δ)*(Q q^((1/3:ℝ)-δ)*κ q^4)) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [mixed_major_kernel_conductor_identity (Q q) L δ (hQ q) hL0.le]
        ring
      _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hpow : L^((19/6:ℝ)+δ)*L^((1/3:ℝ)+δ)=L^((7/2:ℝ)+2*δ) := by
    rw [← Real.rpow_add hL0]
    congr 1 <;> ring
  have hfac : 0≤CK*V*(D^finrank ℚ K)⁻¹ := by positivity
  have hbracket :
      Z^4*(∑q,Q q^(-(1/2):ℝ)*κ q^4)+L^((19/6:ℝ)+δ)*(∑q,Q q^((1/3:ℝ)-δ)*κ q^4) ≤
      (CN+CT)*(Z^4+L^((7/2:ℝ)+2*δ)) := by
    calc
      _ ≤ Z^4*CN+L^((19/6:ℝ)+δ)*(CT*L^((1/3:ℝ)+δ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hs0 (pow_nonneg hZ 4))
          (mul_le_mul_of_nonneg_left hs1 (Real.rpow_nonneg hL0.le _))
      _ = CN*Z^4+CT*L^((7/2:ℝ)+2*δ) := by
        calc
          _ = CN*Z^4+CT*(L^((19/6:ℝ)+δ)*L^((1/3:ℝ)+δ)) := by ring
          _ = _ := by rw [hpow]
      _ ≤ _ := by
        exact (add_le_add
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCT.le) (pow_nonneg hZ 4))
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCN.le)
            (Real.rpow_nonneg hL0.le ((7/2:ℝ)+2*δ)))).trans_eq (by ring)
  have hu := traceHaar_integral_finite_union_le
    (fun q : traceRationalCenters K N => traceMajorArc D L (traceCenterRepresentative q))
    (fun q => traceMajorArc_measurableSet _ _ hD _) f hfc hfn
  calc
    _ ≤ ∑q : traceRationalCenters K N,∫θ in traceMajorArc D L (traceCenterRepresentative q),f θ ∂traceHaar := by
      simpa only [traceMajorArcUnion_eq_finite_union,N] using hu
    _ ≤ ∑q : traceRationalCenters K N,CK*(V*κ q^4)*(D^finrank ℚ K)⁻¹ *
        (Z^4*Q q^(-(1/2):ℝ)+Q q^((7/2):ℝ)*(L/Q q)^((19/6:ℝ)+δ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hk D L (V*κ q^4) Z hD (by positivity) hZ (traceCenterRepresentative q)
        (hQL q) f hfc hfn (hpoint _)
    _ = _ := hmass
    _ ≤ CK*V*(D^finrank ℚ K)⁻¹*((CN+CT)*(Z^4+L^((7/2:ℝ)+2*δ))) :=
      mul_le_mul_of_nonneg_left hbracket hfac
    _ = _ := by ring

#print axioms mixedMajorKernel_union_bound
end WaringSiegel.WSL4
