import WaringSiegel.WSL4ArchQuadraticMajor
import Mathlib.Algebra.Order.Chebyshev

/-! # The absolute quadratic h-sum on the actual enlarged mixed major arc -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceQuadraticAbs_mixed_major_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ) (hP : 1 ≤ P), 1 ≤ H → H ≤ P → P ≤ H^2 →
      ∀ θ : mixedSpace K, ∀ γ : K,
      θ ∈ productMajorArc (inverseDifferent K) (P^2*H) (L*P^finrank ℚ K) γ →
      ∀ U : Finset (𝓞 K), (∀ h ∈ U, h ≠ 0) →
      (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∑ h ∈ U, ‖compactTraceWeylSum 2 w hc P (by linarith)
        (traceTorusMul (3*h) (Submodule.Quotient.mk θ))‖) ≤
        C*H^finrank ℚ K*P^finrank ℚ K*P^ε *
          (((traceConductor γ).absNorm:ℝ)*productArcWeight (P^2*H)
            (θ-mixedEmbedding K γ))^(-(1/2):ℝ) := by
  obtain ⟨C,hC,hb⟩ := compactQuadraticAverage_mixed_major_bound hw hc hsupport
    (show 0<2*ε by positivity) L hL
  let Cb : ℝ := 2*3^finrank ℚ K
  let D := Cb*C
  have hCb : 0<Cb := by dsimp [Cb]; positivity
  have hD : 0<D := mul_pos hCb hC
  refine ⟨D+1,by positivity,fun P H hP hH hHP hPH θ γ hmajor U hU0 hU => ?_⟩
  have hP0 : 0<P := by linarith
  have hH0 : 0<H := by linarith
  let A := ((traceConductor γ).absNorm:ℝ)*productArcWeight (P^2*H) (θ-mixedEmbedding K γ)
  have hA : 0<A := mul_pos
    (Nat.cast_pos.mpr (conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ))
    (productArcWeight_pos _ _)
  let f : 𝓞 K → ℝ := fun h => ‖compactTraceWeylSum 2 w hc P hP0.ne'
    (traceTorusMul (3*h) (Submodule.Quotient.mk θ))‖
  let V := H^finrank ℚ K*P^finrank ℚ K*P^ε*A^(-(1/2):ℝ)
  have hV : 0≤V := by dsimp [V]; positivity
  have hcU : (U.card:ℝ) ≤ Cb*H^finrank ℚ K := integer_box_card_bound U H hH (by
    intro h hh v
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans (hU h hh))
  have hsqsum : (∑ h ∈ U, f h^2) ≤ C*(P^finrank ℚ K)^2*H^finrank ℚ K*P^(2*ε)/A := by
    change compactTraceQuadraticAverage w hc P hP0.ne' U (Submodule.Quotient.mk θ) ≤ _
    rw [compactTraceQuadraticAverage_mk]
    exact hb P H hP hH hHP hPH θ γ hmajor (fun _ => 0) U hU0 hU
  have hp2 : (P^ε)^2=P^(2*ε) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hP0.le]
    congr 1
    ring
  have ha2 : (A^(-(1/2):ℝ))^2=A⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hA.le]
    norm_num only [Nat.cast_ofNat,show (-(1/2):ℝ)*2 = -1 by norm_num,Real.rpow_neg_one]
  have he : (Cb*H^finrank ℚ K)*(C*(P^finrank ℚ K)^2*H^finrank ℚ K*P^(2*ε)/A) = D*V^2 := by
    dsimp only [D,V]
    simp only [mul_pow,hp2,ha2]
    ring
  have hsq : (∑ h ∈ U, f h)^2 ≤ D*V^2 := by
    apply (sq_sum_le_card_mul_sum_sq (s:=U) (f:=f)).trans
    exact (mul_le_mul hcU hsqsum (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (by positivity)).trans_eq he
  have hD2 : D ≤ (D+1)^2 := by nlinarith [sq_nonneg D]
  have hsq' : (∑ h ∈ U, f h)^2 ≤ ((D+1)*V)^2 := by
    exact (hsq.trans (mul_le_mul_of_nonneg_right hD2 (sq_nonneg V))).trans_eq (by ring)
  have hres := (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (by positivity : 0≤D+1) hV)).mp hsq'
  exact hres.trans_eq (by dsimp only [V,A]; ring)

#print axioms compactTraceQuadraticAbs_mixed_major_bound
end WaringSiegel.WSL4
