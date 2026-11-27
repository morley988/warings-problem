import WaringSiegel.WSL4ArchAuxiliarySources

/-! # The exact normalized auxiliary four-by-four main product -/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliary_root_main_product_volumes (rho R P : ℝ) (γ : K) (p : ℕ) (hp : p≠0)
    (β : mixedSpace K) :
    (auxiliaryRootMaskedMain rho R P γ p hp β)^4*(auxiliaryRootScaledMain rho R P γ p β)^4 =
      (P^finrank ℚ K:ℂ)^4*((P/(p:ℝ))^finrank ℚ K:ℂ)^4*
        ((auxiliaryMaskedCubicAverage (fieldCenterCubicCharacter γ) (p:𝓞 K) (Nat.cast_ne_zero.mpr hp))^4*
          (auxiliaryScaledCubicAverage (fieldCenterCubicCharacter γ) (p:𝓞 K))^4)*
        (pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight rho R) (P^3 • β))^8 := by
  unfold auxiliaryRootMaskedMain auxiliaryRootScaledMain
  ring

theorem auxiliary_root_four_by_four_volume (P : ℝ) (p : ℕ) :
    (P^finrank ℚ K:ℂ)^4*((P/(p:ℝ))^finrank ℚ K:ℂ)^4 =
      (((P^finrank ℚ K)^8/((p:ℝ)^finrank ℚ K)^4:ℝ):ℂ) := by
  simp only [div_pow,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

theorem auxiliary_root_main_product (rho R P : ℝ) (γ : K) (p : ℕ) (hp : p≠0)
    (β : mixedSpace K) :
    (auxiliaryRootMaskedMain rho R P γ p hp β)^4*(auxiliaryRootScaledMain rho R P γ p β)^4 =
      (((P^finrank ℚ K)^8/((p:ℝ)^finrank ℚ K)^4:ℝ):ℂ)*
        ((auxiliaryMaskedCubicAverage (fieldCenterCubicCharacter γ) (p:𝓞 K) (Nat.cast_ne_zero.mpr hp))^4*
          (auxiliaryScaledCubicAverage (fieldCenterCubicCharacter γ) (p:𝓞 K))^4)*
        (pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight rho R) (P^3 • β))^8 := by
  rw [auxiliary_root_main_product_volumes,auxiliary_root_four_by_four_volume]

theorem auxiliary_root_main_product_character (rho R P : ℝ) (γ : K) (p : ℕ) (hp : p≠0)
    (ν : 𝓞 K) (β : mixedSpace K) :
    (auxiliaryRootMaskedMain rho R P γ p hp β)^4*(auxiliaryRootScaledMain rho R P γ p β)^4 *
      (fieldCenterCubicCharacter γ).2.1 (-Ideal.Quotient.mk (traceConductor γ) ν) =
      (((P^finrank ℚ K)^8/((p:ℝ)^finrank ℚ K)^4:ℝ):ℂ)*
        auxiliaryCubicCharacterContribution (fieldCenterCubicCharacter γ) (p:𝓞 K)
          (Nat.cast_ne_zero.mpr hp) ν *
        (pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight rho R) (P^3 • β))^8 := by
  rw [auxiliary_root_main_product]
  unfold auxiliaryCubicCharacterContribution
  dsimp only [fieldCenterCubicCharacter]
  ring

#print axioms auxiliary_root_main_product
#print axioms auxiliary_root_main_product_character
end WaringSiegel.WSL4
