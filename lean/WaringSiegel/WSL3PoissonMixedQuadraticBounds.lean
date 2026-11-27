import WaringSiegel.WSL3PoissonMixedQuadraticKernel

/-!
# Genuine major/minor estimates for the actual quadratic average

With X=P^d and T=H^d the minor bound is TX P^ε. The major bound
retains the literal factor 1+X/(Qγ A(2P²H,6θ−γ)). All derivative,
Poisson, summability, and divisor assumptions have been discharged.
-/
noncomputable section
set_option maxHeartbeats 600000
open Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactQuadraticAverage_bound_of_kernel {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 1 ≤ H → H ≤ P →
      ∀ θ : mixedSpace K, ∀ R : ℝ, 1 ≤ R →
      (∑' p : originalLongThinDomain (K:=K) P (2*H), originalLongThinProductDecay (6*θ) P p) ≤
        originalLongThinProductConstant K*(2*H)^finrank ℚ K*R →
      ∀ α : 𝓞 K → mixedSpace K, ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∑ h ∈ U, ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) (α h)‖^2) ≤
        C*P^finrank ℚ K*H^finrank ℚ K*P^ε*R := by
  obtain ⟨C,hC,hb⟩ := compactQuadraticAverage_kernel_bound hw hc hsupport hε
  let A : ℝ := 2*(3:ℝ)^finrank ℚ K
  let B := originalLongThinProductConstant K
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := originalLongThinProductConstant_pos
  refine ⟨C*(A+B*2^finrank ℚ K),by positivity,fun P H hP hH hHP θ R hR hkernel α U hU0 hU => ?_⟩
  have hP0 : 0 < P := by linarith
  have hH0 : 0 < H := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hε1 : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hcard : (U.card:ℝ) ≤ A*H^finrank ℚ K := integer_box_card_bound U H hH
    (fun h hh v => by rw [← normAtPlace_apply]; exact (normAtPlace_le_mixed_norm _ v).trans (hU h hh))
  have hdiag : (U.card:ℝ) ≤ A*H^finrank ℚ K*P^ε*R := by
    apply hcard.trans
    apply (le_mul_of_one_le_right (by positivity) hε1).trans
    exact le_mul_of_one_le_right (by positivity) hR
  have hoff := mul_le_mul_of_nonneg_left hkernel (show 0 ≤ P^ε by positivity)
  have hi : (U.card:ℝ)+P^ε*
      (∑' p : originalLongThinDomain (K:=K) P (2*H), originalLongThinProductDecay (6*θ) P p) ≤
      (A+B*2^finrank ℚ K)*H^finrank ℚ K*P^ε*R := by
    apply (add_le_add hdiag hoff).trans_eq
    dsimp [B]
    rw [mul_pow]
    ring
  exact (hb P H hP hH0 hHP θ α U hU0 hU).trans
    ((mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring))

/-- The required quadratic minor-arc saving for actual finite integer shifts. -/
theorem compactQuadraticAverage_minor_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 1 ≤ H → H ≤ P → P ≤ H^2 →
      ∀ θ : mixedSpace K,
      (∀ γ : K, P^finrank ℚ K <
        (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ):ℝ) *
          productArcWeight (P^2*(2*H)) ((6:mixedSpace K)*θ-mixedEmbedding K γ)) →
      ∀ α : 𝓞 K → mixedSpace K, ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∑ h ∈ U, ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) (α h)‖^2) ≤
        C*P^finrank ℚ K*H^finrank ℚ K*P^ε := by
  obtain ⟨C,hC,hb⟩ := compactQuadraticAverage_bound_of_kernel hw hc hsupport hε
  refine ⟨C,hC,fun P H hP hH hHP hPH θ hminor α U hU0 hU => ?_⟩
  have hk := (originalLongThinProductDecay_minor_bound (6*θ) P (2*H) hP (by linarith)
    (by nlinarith) hminor).2
  simpa only [mul_one] using hb P H hP hH hHP θ 1 le_rfl (by simpa only [mul_one] using hk)
    α U hU0 hU

/-- The actual major-arc quadratic average retains the proved conductor decay. -/
theorem compactQuadraticAverage_major_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 1 ≤ P → 1 ≤ H → H ≤ P → P ≤ H^2 →
      ∀ θ : mixedSpace K, ∀ γ : K,
      (6*θ) ∈ productMajorArc (inverseDifferent K) (P^2*(2*H)) (P^finrank ℚ K) γ →
      ∀ α : 𝓞 K → mixedSpace K, ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      (∑ h ∈ U, ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) (α h)‖^2) ≤
        C*P^finrank ℚ K*H^finrank ℚ K*P^ε*
          longThinMajorFactor (inverseDifferent K) (6*θ) P (2*H) γ := by
  obtain ⟨C,hC,hb⟩ := compactQuadraticAverage_bound_of_kernel hw hc hsupport hε
  refine ⟨C,hC,fun P H hP hH hHP hPH θ γ hmaj α U hU0 hU => ?_⟩
  apply hb P H hP hH hHP θ _
    (longThinMajorFactor_one_le (inverseDifferent K) (inverseDifferent_ne_zero (K:=K))
      (6*θ) P (2*H) (by linarith) γ) _ α U hU0 hU
  exact (originalLongThinProductDecay_major_bound (6*θ) P (2*H) hP (by linarith)
    (by nlinarith) γ hmaj).2

end WaringSiegel.WSL3Poisson
