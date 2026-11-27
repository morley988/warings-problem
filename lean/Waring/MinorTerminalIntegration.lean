import Waring.MajorTerminalExponent
import Waring.CertificateHeight

/-!
# From a checked height residual to an actual minor-terminal integral

The finite certificate controls a residual at every real height.  This file
turns that bound into an actual integral estimate, using the published
restricted mean as an explicit hypothesis.  The dyadic summation and its
epsilon loss are proved; no shell-integral conclusion is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.MinorTerminalIntegration
open MajorTerminalExponent

/-- The genuine full moment supplies every fixed-factor endpoint beyond the
restricted-mean range. This avoids silently extending a source theorem's
stated range. -/
theorem restricted_mean_extend {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (H : α → ℝ) (g : α → ℝ≥0∞)
    {U lam : ℝ} (hU : 1 ≤ U) (hlam : 0 ≤ lam) (K : ℝ≥0∞)
    (hrestricted : ∀ Z : ℝ, 1 ≤ Z → Z ≤ U →
      (∫⁻ x in {x | H x ≤ Z}, g x ∂μ) ≤ K*ENNReal.ofReal (Z^lam))
    (hfull : (∫⁻ x, g x ∂μ) ≤ K*ENNReal.ofReal (U^lam)) :
    ∀ Z : ℝ, 1 ≤ Z →
      (∫⁻ x in {x | H x ≤ Z}, g x ∂μ) ≤ K*ENNReal.ofReal (Z^lam) := by
  intro Z hZ
  by_cases hZU : Z ≤ U
  · exact hrestricted Z hZ hZU
  · calc
      _ ≤ ∫⁻ x, g x ∂μ := setLIntegral_le_lintegral _ _
      _ ≤ K*ENNReal.ofReal (U^lam) := hfull
      _ ≤ K*ENNReal.ofReal (Z^lam) := mul_le_mul_left'
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (zero_le_one.trans hU)
          (le_of_not_ge hZU) hlam)) K

/-- At the Dirichlet height endpoint Q^(k/2), the restricted-mean height
factor is precisely the full-moment excess Q^Delta. -/
theorem height_endpoint_excess {Q k Delta : ℝ} (hQ : 0 ≤ Q) (hk : k ≠ 0) :
    (Q^(k/2))^(2*Delta/k) = Q^Delta := by
  rw [← Real.rpow_mul hQ]
  congr 1
  field_simp

theorem residual_to_height_decay {P ell saving lam E : ℝ} (hP : 1 ≤ P)
    (hres : lam*ell-saving ≤ E) :
    P^(-saving) ≤ P^E*(P^ell)^(-lam) := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  rw [← Real.rpow_mul hPp.le, ← Real.rpow_add hPp]
  exact Real.rpow_le_rpow_of_exponent_le hP (by linarith)

/-- A polynomial height range costs only an arbitrarily small power of P.
The same constant works for every measure, height function, and pointwise
saving satisfying the displayed hypotheses. -/
theorem restricted_terminal_from_residual {B lam ε : ℝ}
    (hB : 0 < B) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α)
        (H ell saving : α → ℝ) (F g : α → ℝ≥0∞),
      Measurable H → Measurable g →
      (∀ᵐ x ∂μ, 1 ≤ H x) → (∀ᵐ x ∂μ, H x ≤ P^B) →
      (∀ᵐ x ∂μ, H x = P^(ell x)) →
      ∀ (A K : ℝ≥0∞) (E : ℝ),
      (∀ᵐ x ∂μ, lam*ell x-saving x ≤ E) →
      (∀ᵐ x ∂μ, F x ≤ A*ENNReal.ofReal (P^(-saving x))) →
      (∀ Z : ℝ, 1 ≤ Z → Z ≤ 4*P^B →
        (∫⁻ x in {x | H x ≤ Z}, g x ∂μ) ≤ K*ENNReal.ofReal (Z^lam)) →
      (∫⁻ x, F x*g x ∂μ) ≤ A*K*ENNReal.ofReal (C*P^(E+ε)) := by
  obtain ⟨C,hC,hmajor⟩ := restricted_major_epsilon (lam:=lam) hlam
    (show 0 < ε/B by positivity)
  refine ⟨C,hC,?_⟩
  intro P hP α _ μ H ell saving F g hH hg hlo hhi hheight A K E hres hpoint hmeans
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hQ : 1 ≤ P^B := Real.one_le_rpow hP hB.le
  have hweighted : ∀ᵐ x ∂μ,
      F x ≤ (A*ENNReal.ofReal (P^E))*ENNReal.ofReal ((H x)^(-lam)) := by
    filter_upwards [hheight,hres,hpoint] with x hx hr hp
    calc
      _ ≤ A*ENNReal.ofReal (P^(-saving x)) := hp
      _ ≤ A*ENNReal.ofReal (P^E*(P^(ell x))^(-lam)) :=
        mul_le_mul_left' (ENNReal.ofReal_le_ofReal (residual_to_height_decay hP hr)) A
      _ = _ := by rw [← hx,ENNReal.ofReal_mul (Real.rpow_nonneg hPp.le _)]; ac_rfl
  have hh := hmajor (P^B) hQ α μ H F g hH hg hlo hhi
    (A*ENNReal.ofReal (P^E)) K hweighted hmeans
  have hexp : (P^B)^(max 0 (lam-lam)+ε/B) = P^ε := by
    rw [sub_self,max_self,zero_add,← Real.rpow_mul hPp.le]
    congr 1
    field_simp
  rw [hexp] at hh
  have hid : (A*ENNReal.ofReal (P^E))*K*ENNReal.ofReal (C*P^ε) =
      A*K*ENNReal.ofReal (C*P^(E+ε)) := by
    rw [Real.rpow_add hPp]
    simp only [ENNReal.ofReal_mul hC.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg hPp.le E)]
    ac_rfl
  exact hid ▸ hh

/-- The certificate's literal capped saving has exactly the required residual
form. This bridge uses its real-valued definitions, not an independently
transcribed exponent formula. -/
theorem certificate_residual_to_height_decay
    (k : Nat) (p : Certificate.Policy) (coefficient : Certificate.Curve)
    (piece : Certificate.Piece) (base slope scale : Certificate.Q)
    {P ell E : ℝ} (hP : 1 ≤ P)
    (hres : Certificate.pieceResidualReal k p coefficient piece base slope scale ell ≤ E) :
    P^((base : ℝ)-(scale : ℝ)*min 1
      (Certificate.pieceSavingReal k p coefficient piece ell)) ≤
      P^E*(P^ell)^(-(slope : ℝ)) := by
  have hr : (slope : ℝ)*ell-
      ((scale : ℝ)*min 1 (Certificate.pieceSavingReal k p coefficient piece ell)-(base : ℝ)) ≤ E := by
    simp only [Certificate.pieceResidualReal,Height.residual] at hres
    linarith
  have hh := residual_to_height_decay hP hr
  convert hh using 1 <;> congr 1 <;> ring

#print axioms restricted_terminal_from_residual
#print axioms certificate_residual_to_height_decay
end Waring.MinorTerminalIntegration
