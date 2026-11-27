import WaringSiegel.WSL3PoissonMixedPhase
import WaringSiegel.WSL2MomentCubicCompressionGrowth

/-! # Support and cardinality bounds for actual differencing boxes -/
noncomputable section
open Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactIntegerSupport_norm_bound {w : mixedSpace K → ℂ} (hc : HasCompactSupport w)
    (hw : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) (P : ℝ) (hP : 0 < P)
    {x : 𝓞 K} (hx : x ∈ compactIntegerSupport w hc P hP.ne') :
    ‖mixedEmbedding K (x:K)‖ ≤ P := by
  have hb := hw _ ((mem_compactIntegerSupport w hc P hP.ne' x).mp hx)
  rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hP)] at hb
  calc
    _ = P * (P⁻¹ * ‖mixedEmbedding K (x:K)‖) := by field_simp
    _ ≤ P * 1 := mul_le_mul_of_nonneg_left hb hP.le
    _ = P := mul_one _

theorem additiveDifferences_norm_bound (S : Finset (𝓞 K)) (P : ℝ)
    (hS : ∀ x ∈ S, ‖mixedEmbedding K (x:K)‖ ≤ P)
    {h : 𝓞 K} (hh : h ∈ additiveDifferences S) :
    ‖mixedEmbedding K (h:K)‖ ≤ 2*P := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
  have he : mixedEmbedding K ((p.1-p.2:𝓞 K):K) =
      mixedEmbedding K (p.1:K)-mixedEmbedding K (p.2:K) := by simp only [map_sub]
  rw [he]
  have h1 := hS p.1 (Finset.mem_product.mp hp).1
  have h2 := hS p.2 (Finset.mem_product.mp hp).2
  exact (norm_sub_le _ _).trans (by linarith)

def shiftBoxConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  2*(3:ℝ)^(Module.finrank ℚ K)*2^(Module.finrank ℚ K)

theorem shiftBoxConstant_pos : 0 < shiftBoxConstant K := by unfold shiftBoxConstant; positivity

theorem shiftBox_card_bound (P : ℝ) (hP : 1 ≤ P) (H : Finset (𝓞 K))
    (hH : ∀ h ∈ H, ‖mixedEmbedding K (h:K)‖ ≤ 2*P) :
    (H.card:ℝ) ≤ shiftBoxConstant K * P^(Module.finrank ℚ K) := by
  have hb := integer_box_card_bound H (2*P) (by linarith) (fun h hh v => by
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans (hH h hh))
  simpa only [shiftBoxConstant,mul_pow,← mul_assoc] using hb

theorem shiftProducts_mixed_norm_bound (P : ℝ) (hP : 0 ≤ P) (H : Finset (𝓞 K))
    (hH : ∀ h ∈ H, ‖mixedEmbedding K (h:K)‖ ≤ 2*P)
    {y : 𝓞 K} (hy : y ∈ shiftProducts H) :
    ‖mixedEmbedding K (y:K)‖ ≤ P*(4*P) := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
  have he : mixedEmbedding K ((p.1*p.2:𝓞 K):K) =
      mixedEmbedding K (p.1:K)*mixedEmbedding K (p.2:K) := by simp only [map_mul]
  rw [he]
  have hb := mul_le_mul (hH p.1 (Finset.mem_product.mp hp).1)
    (hH p.2 (Finset.mem_product.mp hp).2) (norm_nonneg _) (by positivity)
  exact (norm_mul_le _ _).trans (hb.trans_eq (by ring))

theorem normalized_shift_norm_le_two (P : ℝ) (hP : 0 < P) {h : 𝓞 K}
    (hh : ‖mixedEmbedding K (h:K)‖ ≤ 2*P) :
    ‖P⁻¹ • mixedEmbedding K (h:K)‖ ≤ 2 := by
  rw [_root_.norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hP)]
  calc
    _ ≤ P⁻¹ * (2*P) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hP.le)
    _ = 2 := by field_simp

end WaringSiegel.WSL3Poisson
