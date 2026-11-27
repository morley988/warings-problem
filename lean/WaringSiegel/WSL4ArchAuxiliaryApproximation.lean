import WaringSiegel.WSL4ArchAuxiliarySources

/-! # Prime-uniform arbitrary-order replacements for the two literal auxiliary sources -/
noncomputable section
set_option maxHeartbeats 1700000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def auxiliaryRootArcRatio (P : ℝ) (p : ℕ) (γ : K) (β : mixedSpace K) : ℝ :=
  (p:ℝ)^finrank ℚ K*powerArcRatio 3 P β (traceConductor γ)

theorem auxiliaryRootArcRatio_nonneg (P : ℝ) (hP : 0<P) (p : ℕ) (γ : K) (β : mixedSpace K) :
    0≤auxiliaryRootArcRatio P p γ β :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (powerArcRatio_nonneg 3 P hP β _)

theorem masked_powerArcRatio_le_auxiliary (P : ℝ) (hP : 0<P) (p : ℕ) (hp : p≠0)
    (γ : K) (β : mixedSpace K) :
    powerArcRatio 3 P β (auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K)) ≤
      auxiliaryRootArcRatio P p γ β := by
  have hN : ((auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K)).absNorm:ℝ) ≤
      ((traceConductor γ).absNorm:ℝ)*(p:ℝ)^finrank ℚ K := by
    exact_mod_cast auxiliaryCommonModulus_nat_norm_le (traceConductor γ) (traceConductor_ne_zero γ) p hp
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hN (productArcWeight_pos (P^3) β).le) (pow_nonneg hP.le (finrank ℚ K))
  exact hh.trans_eq (by unfold auxiliaryRootArcRatio powerArcRatio; ring)

theorem scaled_powerArcRatio_eq_auxiliary (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p)
    (γ : K) (β : mixedSpace K) :
    powerArcRatio 3 (P/(p:ℝ)) ((p:ℝ)^3 • β) (traceConductor γ) =
      auxiliaryRootArcRatio P p γ β := by
  unfold auxiliaryRootArcRatio powerArcRatio
  rw [auxiliary_scaled_productArcWeight P (p:ℝ) (Nat.cast_pos.mpr hp) β,div_pow]
  field_simp
  <;> ring

theorem auxiliaryRootMaskedSource_main_error (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (p : ℕ) (hp : p≠0) (P : ℝ) (hP : 0<P) (β : mixedSpace K),
      ‖compactCoprimeTraceCubicSum (K:=K) (smoothWeightSchwartz (K:=K) rho R hrho hR) P p
          (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0 -
        auxiliaryRootMaskedMain rho R P γ p hp β‖ ≤
        C*P^finrank ℚ K*(auxiliaryRootArcRatio P p γ β)^N*(1+auxiliaryRootArcRatio P p γ β) := by
  obtain ⟨C,hC,hb⟩ := smoothPower_residue_main_error_arcWeight (K:=K) 3 rho R hrho hR N
  refine ⟨C,hC,fun γ p hp P hP β => ?_⟩
  let M := auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K)
  have hM : M≠0 := auxiliaryCommonModulus_ne_zero _ (traceConductor_ne_zero γ) _ (Nat.cast_ne_zero.mpr hp)
  letI := idealResidueFintype M hM
  have hh := hb M hM (auxiliaryMaskedResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K))
    (auxiliaryMaskedResidueWeight_norm_le_one (fieldCenterCubicCharacter γ) (p:𝓞 K)) P hP β
  have ha0 := powerArcRatio_nonneg 3 P hP β M
  have ha := masked_powerArcRatio_le_auxiliary P hP p hp γ β
  have hA := auxiliaryRootArcRatio_nonneg P hP p γ β
  rw [auxiliary_masked_root_source_center,auxiliaryRootMaskedMain_eq_raw]
  apply hh.trans
  have hprod := mul_le_mul (pow_le_pow_left₀ ha0 ha N) (add_le_add_left ha 1)
    (by linarith : 0≤1+powerArcRatio 3 P β M) (pow_nonneg hA N)
  have hh' := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le (pow_nonneg hP.le (finrank ℚ K)))
  simpa only [mul_assoc] using hh'

theorem auxiliaryRootScaledSource_main_error (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (p : ℕ) (hp : 0<p) (P : ℝ) (hP : 0<P) (β : mixedSpace K),
      ‖smoothTraceSource (K:=K) 3 rho R hrho hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp)).ne'
          (traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β))) -
        auxiliaryRootScaledMain rho R P γ p β‖ ≤
        C*(P/(p:ℝ))^finrank ℚ K*(auxiliaryRootArcRatio P p γ β)^N*(1+auxiliaryRootArcRatio P p γ β) := by
  obtain ⟨C,hC,hb⟩ := smoothPower_residue_main_error_arcWeight (K:=K) 3 rho R hrho hR N
  refine ⟨C,hC,fun γ p hp P hP β => ?_⟩
  letI := idealResidueFintype (traceConductor γ) (traceConductor_ne_zero γ)
  have hpR : 0<(p:ℝ) := Nat.cast_pos.mpr hp
  have hh := hb (traceConductor γ) (traceConductor_ne_zero γ)
    (auxiliaryScaledResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K))
    (auxiliaryScaledResidueWeight_norm_le_one (fieldCenterCubicCharacter γ) (p:𝓞 K)) (P/(p:ℝ)) (div_pos hP hpR) ((p:ℝ)^3 • β)
  rw [auxiliary_scaled_root_frequency P (p:ℝ) hpR β,
    scaled_powerArcRatio_eq_auxiliary P hP p hp γ β] at hh
  rw [auxiliary_scaled_root_source_center rho R hrho hR P hP p hp γ β,auxiliaryRootScaledMain_eq_raw]
  exact hh

#print axioms auxiliaryRootMaskedSource_main_error
#print axioms auxiliaryRootScaledSource_main_error
end WaringSiegel.WSL4
