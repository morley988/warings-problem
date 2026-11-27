import WaringLinear.MixedSupport

/-! # Removal of the minor-arc defect in an even restricted moment

The full-torus positivity comparison permits one ordinary variable. On the
major arcs a scalar splitting inequality absorbs half of the unknown
moment. A pointwise saving on the ordinary variable pays for the defect on
the minor arcs.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
open WaringSiegel WaringSiegel.WSL2

namespace WaringLinear

theorem one_factor_split {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (s : ℕ) :
    x * y^s ≤ (2*x)^(s+1) + (1/2 : ℝ) * y^(s+1) := by
  by_cases h : y ≤ 2*x
  · have hp : y^s ≤ (2*x)^s := pow_le_pow_left₀ hy h s
    have hxx : x ≤ 2*x := by linarith
    have hm := mul_le_mul hxx hp (pow_nonneg hy _) (by positivity : 0 ≤ 2*x)
    rw [pow_succ']
    exact hm.trans (le_add_of_nonneg_right (by positivity))
  · have hxy : x ≤ (1/2 : ℝ)*y := by linarith
    have hm := mul_le_mul_of_nonneg_right hxy (pow_nonneg hy s)
    calc
      _ ≤ ((1/2 : ℝ)*y)*y^s := hm
      _ = (1/2 : ℝ)*y^(s+1) := by rw [pow_succ']; ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

variable {T : Type*} [MeasurableSpace T]

/-- Explicit major/minor bootstrap; m is the restricted input order and d
is the number of copies on which the trivial height bound is used. -/
theorem absorb_mixed_moment (μ : Measure T) (M : Set T) (hM : MeasurableSet M)
    (F f : T → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hf0 : ∀ x, 0 ≤ f x)
    (m d : ℕ) (P B : ℝ) (hB : 0 ≤ B)
    (hBox : ∀ x ∈ Mᶜ, F x ≤ P) (hMinor : ∀ x ∈ Mᶜ, f x ≤ B)
    (hI : Integrable (fun x => F x^(m+d+1)) μ)
    (hJ : Integrable (fun x => f x^(m+d+1)) μ)
    (hr : Integrable (fun x => F x^m) μ)
    (hmix : Integrable (fun x => f x*F x^(m+d)) μ)
    (hSupport : (∫ x, F x^(m+d+1) ∂μ) ≤ ∫ x, f x*F x^(m+d) ∂μ) :
    (∫ x, F x^(m+d+1) ∂μ) ≤
      2*((2:ℝ)^(m+d+1)*(∫ x in M, f x^(m+d+1) ∂μ) +
        B*P^d*(∫ x in Mᶜ, F x^m ∂μ)) := by
  have hMajor : (∫ x in M, f x * F x^(m+d) ∂μ) ≤
      (2:ℝ)^(m+d+1)*(∫ x in M, f x^(m+d+1) ∂μ) +
      (1/2 : ℝ)*(∫ x in M, F x^(m+d+1) ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
    · apply setIntegral_mono_on hmix.integrableOn
        (((hJ.const_mul _).add (hI.const_mul _)).integrableOn) hM
      intro x _
      simpa only [mul_pow] using one_factor_split (hf0 x) (hF0 x) (m+d)
    · exact (hJ.const_mul _).integrableOn
    · exact (hI.const_mul _).integrableOn
  have hMinorBound : (∫ x in Mᶜ, f x * F x^(m+d) ∂μ) ≤
      B*P^d*(∫ x in Mᶜ, F x^m ∂μ) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hmix.integrableOn (hr.const_mul _).integrableOn hM.compl
    intro x hx
    rw [pow_add]
    calc
      _ = (f x * F x^d)* F x^m := by ring
      _ ≤ (B*P^d)* F x^m := mul_le_mul_of_nonneg_right
        (mul_le_mul (hMinor x hx) (pow_le_pow_left₀ (hF0 x) (hBox x hx) d)
          (pow_nonneg (hF0 x) _) hB) (pow_nonneg (hF0 x) _)
  have hsub : (∫ x in M, F x^(m+d+1) ∂μ) ≤ ∫ x, F x^(m+d+1) ∂μ :=
    setIntegral_le_integral hI (Filter.Eventually.of_forall (fun x => pow_nonneg (hF0 x) _))
  rw [← integral_add_compl hM hmix] at hSupport
  linarith

/-- The ordinary minor saving pays for a restricted moment defect whenever the
saving is at least as large as the defect. The output gives the constants and
a zero-defect exponent. -/
theorem loss_free_of_defect (μ : Measure T) (M : Set T) (hM : MeasurableSet M)
    (F f : T → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hf0 : ∀ x, 0 ≤ f x)
    (m d k : ℕ) (P C B A D ρ E : ℝ) (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : E ≤ ρ)
    (hBox : ∀ x ∈ Mᶜ, F x ≤ C*P)
    (hMinor : ∀ x ∈ Mᶜ, f x ≤ B*P^(1-ρ))
    (hI : Integrable (fun x => F x^(m+d+1)) μ)
    (hJ : Integrable (fun x => f x^(m+d+1)) μ)
    (hr : Integrable (fun x => F x^m) μ)
    (hmix : Integrable (fun x => f x*F x^(m+d)) μ)
    (hSupport : (∫ x, F x^(m+d+1) ∂μ) ≤ ∫ x, f x*F x^(m+d) ∂μ)
    (hMajor : (∫ x in M, f x^(m+d+1) ∂μ) ≤ A*P^((m:ℝ)+d+1-k))
    (hRestricted : (∫ x, F x^m ∂μ) ≤ D*P^((m:ℝ)-k+E)) :
    (∫ x, F x^(m+d+1) ∂μ) ≤
      2*((2:ℝ)^(m+d+1)*A + B*C^d*D)*P^((m:ℝ)+d+1-k) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hMinor0 : 0 ≤ B*P^(1-ρ) := by positivity
  have hsub : (∫ x in Mᶜ, F x^m ∂μ) ≤ D*P^((m:ℝ)-k+E) :=
    (setIntegral_le_integral hr (Filter.Eventually.of_forall
      (fun x => pow_nonneg (hF0 x) m))).trans hRestricted
  have hpow : P^(1-ρ) * P^d * P^((m:ℝ)-k+E) ≤ P^((m:ℝ)+d+1-k) := by
    rw [← Real.rpow_natCast P d, ← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
    apply Real.rpow_le_rpow_of_exponent_le hP
    linarith
  have hleft := absorb_mixed_moment μ M hM F f hF0 hf0 m d (C*P)
    (B*P^(1-ρ)) hMinor0 hBox hMinor hI hJ hr hmix hSupport
  have hscaled :
      B*P^(1-ρ)*(C*P)^d*(D*P^((m:ℝ)-k+E)) ≤
      B*C^d*D*P^((m:ℝ)+d+1-k) := by
    rw [mul_pow]
    calc
      _ = (B*C^d*D) * (P^(1-ρ)*P^d*P^((m:ℝ)-k+E)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hMajor (by positivity : 0 ≤ (2:ℝ)^(m+d+1))
  have h2 := (mul_le_mul_of_nonneg_left hsub
    (by positivity : 0 ≤ B*P^(1-ρ)*(C*P)^d)).trans hscaled
  nlinarith only [hleft,h1,h2]

#print axioms absorb_mixed_moment
#print axioms loss_free_of_defect

end WaringLinear
