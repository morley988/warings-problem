import Waring.PolicyCompletionAdmissibleLower
import Waring.RestrictedSmoothHeightMean

/-! # Restricted height means from genuine even-moment admissibility

The necessary exponent bounds are consequences of actual admissibility.
This removes them from the source interface used by certificate terminal
integration, including at a shorter power-scaled length.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.PolicyCompletionRestrictedMean
open SmoothMoments RestrictedSmoothArcs

theorem even_excess_height_lintegral {k r : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r)
    {Δ ε : ℝ} (hadm : AdmissibleExcess k (2*r) Δ) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ Z R : ℝ,1 ≤ Z → 1 ≤ R → R ≤ P^η →
      (∫⁻ x in {x | RationalHeight.height (P^k) x ≤ Z},
        ENNReal.ofReal (‖smoothWeyl k P R x‖^(2*r)) ∂(volume.restrict (Set.Ioc 0 1))) ≤
        ENNReal.ofReal (C*P^(((2*r : ℕ) : ℝ)-(k : ℝ)+ε))*
          ENNReal.ofReal (Z^(2*Δ/(k : ℝ))) := by
  have hl := admissibleExponent_even_ge_one hr hadm
  have hd := admissibleExcess_even_nonneg hadm
  have hexp : (((2*r : ℕ) : ℝ)-(k : ℝ)+Δ)-((2*r : ℕ) : ℝ)+(k : ℝ)=Δ := by ring
  simpa only [hexp] using restricted_smooth_height_lintegral hk
    (show 1 ≤ 2*r by omega) hadm hl (by rw [hexp]; exact hd) hε

/-- The scale exponent is fixed before eta is chosen, so the cutoff
condition remains uniform at Q=P^q. -/
theorem even_excess_height_lintegral_power_scale {k r : ℕ}
    (hk : 1 ≤ k) (hr : 1 ≤ r) {Δ q ε : ℝ} (hq : 0 < q)
    (hadm : AdmissibleExcess k (2*r) Δ) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ Z R : ℝ,1 ≤ Z → 1 ≤ R → R ≤ P^η →
      (∫⁻ x in {x | RationalHeight.height (P^((k : ℝ)*q)) x ≤ Z},
        ENNReal.ofReal (‖smoothWeyl k (P^q) R x‖^(2*r))
          ∂(volume.restrict (Set.Ioc 0 1))) ≤
        ENNReal.ofReal (C*P^(((((2*r : ℕ) : ℝ)-(k : ℝ))*q)+ε))*
          ENNReal.ofReal (Z^(2*Δ/(k : ℝ))) := by
  obtain ⟨η,hη,C,hC,hbound⟩ := even_excess_height_lintegral hk hr hadm (div_pos hε hq)
  refine ⟨q*η,mul_pos hq hη,C,hC,?_⟩
  intro P hP Z R hZ hR hRP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hQ1 : 1 ≤ P^q := Real.one_le_rpow hP hq.le
  have hRQ : R ≤ (P^q)^η := by rwa [← Real.rpow_mul hPp.le]
  have hh : (P^q)^k=P^((k : ℝ)*q) := by
    rw [← Real.rpow_mul_natCast hPp.le,mul_comm q (k : ℝ)]
  have hs : (P^q)^(((2*r : ℕ) : ℝ)-(k : ℝ)+ε/q)=
      P^(((((2*r : ℕ) : ℝ)-(k : ℝ))*q)+ε) := by
    rw [← Real.rpow_mul hPp.le]
    congr 1
    field_simp
    <;> ring
  simpa only [hh,hs] using hbound (P^q) hQ1 Z R hZ hR hRQ

#print axioms even_excess_height_lintegral
#print axioms even_excess_height_lintegral_power_scale
end Waring.PolicyCompletionRestrictedMean
