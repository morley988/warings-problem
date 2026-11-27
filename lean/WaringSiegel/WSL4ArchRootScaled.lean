import WaringSiegel.WSL4ArchRootMasked
import WaringSiegel.WSL4MajorSources
import WaringSiegel.WSL4MajorScaling

/-! # The actual small cubic source under the auxiliary p³ frequency multiplier -/
noncomputable section
set_option maxHeartbeats 1300000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem natCast_smul_mixed (p : ℕ) (θ : mixedSpace K) :
    (p:ℝ) • θ=(p:mixedSpace K)*θ := by
  simpa only [nsmul_eq_mul] using Nat.cast_smul_eq_nsmul ℝ p θ

theorem auxiliary_scaled_trace_center (p : ℕ) (γ : K) (β : mixedSpace K) :
    traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β)) =
      Submodule.Quotient.mk (mixedEmbedding K ((p:K)^3*γ)+(p:ℝ)^3 • β) := by
  rw [traceTorusMul_mk]
  have he : (p:ℝ)^3 • β=(p:mixedSpace K)^3*β := by
    calc
      (p:ℝ)^3 • β = (p:ℝ) • ((p:ℝ) • ((p:ℝ) • β)) := by
        simp only [smul_smul]
        congr 1
        ring
      _ = (p:mixedSpace K)^3*β := by
        simp only [natCast_smul_mixed]
        ring
  simp only [RingOfIntegers.coe_eq_algebraMap,map_pow,map_mul,map_natCast]
  rw [he]
  congr 1
  ring

theorem auxiliary_scaled_productArcWeight (P p : ℝ) (hp : 0<p) (β : mixedSpace K) :
    productArcWeight ((P/p)^3) (p^3 • β)=productArcWeight (P^3) β := by
  unfold productArcWeight
  apply Finset.prod_congr rfl
  intro v hv
  rw [normAtPlace_smul,abs_of_pos (pow_pos hp 3)]
  congr 2
  field_simp [hp.ne']
  <;> ring

theorem smoothRootCubic_center_arc_packing_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (κ : ℝ), 0≤κ →
      (∀ ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖≤((traceConductor γ).absNorm:ℝ)*κ) →
      ∀ P : ℝ, 0<P → ∀ β : mixedSpace K,
      ‖smoothPowerCenterSource 3 rho R P γ β‖ ≤
        C*κ*P^finrank ℚ K*(productArcWeight (P^3) β)^(-(1/2):ℝ)*
          (1+((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) β/P^finrank ℚ K) := by
  obtain ⟨C,hC,hb⟩ := smoothRootCubic_center_packing_bound (K:=K) rho R hrho hR
  refine ⟨C,hC,fun γ κ hκ hfinite P hP β => ?_⟩
  have hA := productArcWeight_pos (P^3) β
  have hfreq : (productArcWeight (P^3) β)^((1:ℝ)/2) ≤
      cubicProductStationaryWeight (P^3 • β) :=
    (productArcWeight_rpow_le_frequencyWeight _ (pow_nonneg hP.le _) _ (by norm_num) _).trans
      (cubicProductFrequencyWeight_le_stationary le_rfl _)
  have hh := div_le_div_of_nonneg_left (show 0≤C*κ*P^finrank ℚ K by positivity)
    (Real.rpow_pos_of_pos hA ((1:ℝ)/2)) hfreq
  apply (hb γ κ hκ hfinite P hP β).trans
  apply (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq
  rw [Real.rpow_neg hA.le]
  rfl

theorem smoothRootCubic_scaled_packing_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (p : ℕ) (hp : 0<p) (κ : ℝ), 0≤κ →
      (∀ ξ : (inverseDifferent K*(traceConductor ((p:K)^3*γ) : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 ((p:K)^3*γ) (mixedEmbedding K (ξ:K))‖≤
          ((traceConductor ((p:K)^3*γ)).absNorm:ℝ)*κ) →
      ∀ (P : ℝ) (hP : 0<P) (β : mixedSpace K),
      ‖smoothTraceSource 3 rho R hrho hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp)).ne'
        (traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β)))‖ ≤
        C*κ*(P/(p:ℝ))^finrank ℚ K*(productArcWeight (P^3) β)^(-(1/2):ℝ)*
          (1+((traceConductor ((p:K)^3*γ)).absNorm:ℝ)*productArcWeight (P^3) β/(P/(p:ℝ))^finrank ℚ K) := by
  obtain ⟨C,hC,hb⟩ := smoothRootCubic_center_arc_packing_bound (K:=K) rho R hrho hR
  refine ⟨C,hC,fun γ p hp κ hκ hfinite P hP β => ?_⟩
  have hpR : 0<(p:ℝ) := Nat.cast_pos.mpr hp
  rw [auxiliary_scaled_trace_center,smoothTraceSource_center_eq]
  have hh := hb ((p:K)^3*γ) κ hκ hfinite (P/(p:ℝ)) (div_pos hP hpR) ((p:ℝ)^3 • β)
  simpa only [auxiliary_scaled_productArcWeight P (p:ℝ) hpR β] using hh

#print axioms auxiliary_scaled_trace_center
#print axioms auxiliary_scaled_productArcWeight
#print axioms smoothRootCubic_scaled_packing_bound
end WaringSiegel.WSL4
