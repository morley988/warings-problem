import Waring.EndgameCompletionProductRepresentation

/-! # Uniform product-weight moment bounds -/

noncomputable section
namespace Waring.EndgameCompletion
open SmoothMoments

theorem productMoment_even_power_transfer (L r : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ k M : ℕ,1≤M → ∀ B exponent : ℝ,0≤B →
      smoothMoment k (2*r) ((M : ℝ)^L) M≤B*((M : ℝ)^L)^exponent →
      productMoment k (2*r) L M≤(C*B)*((M : ℝ)^L)^(exponent+ε) := by
  obtain ⟨C,hC,h⟩ := productMoment_even_le_smooth L r hε
  refine ⟨C,hC,?_⟩
  intro k M hM B exponent _ hb
  have hp : 0<(M : ℝ)^L := pow_pos (by exact_mod_cast (show 0<M by omega)) _
  calc
    _ ≤ C*((M : ℝ)^L)^ε*smoothMoment k (2*r) ((M : ℝ)^L) M := h k M hM
    _ ≤ C*((M : ℝ)^L)^ε*(B*((M : ℝ)^L)^exponent) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [Real.rpow_add hp]; ring

theorem degree8_product90_bound (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ M : ℕ,1≤M →
      productMoment 8 90 L M≤C*((M : ℝ)^L)^(82+ε) := by
  obtain ⟨A,hA,htransfer⟩ := productMoment_even_power_transfer L 45 hε
  obtain ⟨B,hB,hstrong⟩ := degree8_smooth90_strong
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro M hM
  apply htransfer 8 M hM B 82 hB.le
  simpa only [Nat.cast_pow,Real.rpow_ofNat] using
    hstrong (M^L) (one_le_pow₀ hM) M

/-- Eta is selected before the product-box rank. Once L*eta≥1, the same
smoothness range applies to every product scale P=M^L. -/
theorem product_admissible_pair {k r s : ℕ} {lam mu ε : ℝ}
    (hr : AdmissibleExponent k (2*r) lam) (hs : AdmissibleExponent k (2*s) mu)
    (hε : 0<ε) :
    ∃ η : ℝ,0<η ∧ ∀ L : ℕ,∃ C : ℝ,0<C ∧ ∃ P₀ : ℝ,1≤P₀ ∧
      ∀ M : ℕ,1≤M → P₀≤(M : ℝ)^L → 1≤(L : ℝ)*η →
        productMoment k (2*r) L M≤C*((M : ℝ)^L)^(lam+ε) ∧
        productMoment k (2*s) L M≤C*((M : ℝ)^L)^(mu+ε) := by
  obtain ⟨η,hη,B,hB,P₀,hP₀,hpair⟩ := admissibleExponent_pair hr hs (half_pos hε)
  refine ⟨η,hη,?_⟩
  intro L
  obtain ⟨A,hA,htr⟩ := productMoment_even_power_transfer L r (half_pos hε)
  obtain ⟨D,hD,hts⟩ := productMoment_even_power_transfer L s (half_pos hε)
  refine ⟨max (A*B) (D*B),(mul_pos hA hB).trans_le (le_max_left _ _),P₀,hP₀,?_⟩
  intro M hM hP hL
  have hb := hpair ((M : ℝ)^L) hP M (by exact_mod_cast hM)
    (product_scale_smoothness hM hL)
  constructor
  · have hh := htr k M hM B (lam+ε/2) hB.le hb.1
    rw [show lam+ε/2+ε/2=lam+ε by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  · have hh := hts k M hM B (mu+ε/2) hB.le hb.2
    rw [show mu+ε/2+ε/2=mu+ε by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))

#print axioms degree8_product90_bound
#print axioms product_admissible_pair
end Waring.EndgameCompletion
