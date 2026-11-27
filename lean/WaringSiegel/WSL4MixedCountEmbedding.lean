import WaringSiegel.WSL3PoissonMixedCompactCount
import WaringSiegel.WSL4ArchBump

/-! # Injective comparison of actual mixed solution counts with smooth majorants -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem sum_comp_le_sum_of_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, w (f a)) ≤ ∑ b, w b := by
  calc
    _ = ∑ b ∈ Finset.univ.image f, w b :=
      (Finset.sum_image (fun a _ b _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => hw b)

theorem nearZero_scaled_eq_one (P : ℝ) (hP : 0 < P) {x : 𝓞 K}
    (hx : ‖mixedEmbedding K (x : K)‖ ≤ P/2) :
    nearZeroSchwartz (P⁻¹ • mixedEmbedding K (x : K)) = 1 := by
  apply nearZeroSchwartz_majorant.2.2.1
  rw [_root_.norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hP)]
  calc
    _ ≤ P⁻¹*(P/2) := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hP.le)
    _ = _ := by field_simp

theorem nearZero_scaled_mem_support (P : ℝ) (hP : 0 < P) {x : 𝓞 K}
    (hx : ‖mixedEmbedding K (x : K)‖ ≤ P/2) :
    x ∈ compactIntegerSupport nearZeroSchwartz nearZeroSchwartz_majorant.2.1 P hP.ne' := by
  apply (mem_compactIntegerSupport _ _ _ _ _).mpr
  rw [nearZero_scaled_eq_one P hP hx]
  exact one_ne_zero

def mixedBoxCount (H Z M Y : Finset (𝓞 K)) : ℕ :=
  Fintype.card {p : H × ((Z × M) × ((Y × Y) × (Y × Y))) //
    mixedWeightedPhase (fun h : H => (h : 𝓞 K)) (fun z : Z => (z : 𝓞 K))
      (fun m : M => (m : 𝓞 K)) (fun y : Y => (y : 𝓞 K)) p = 0}

theorem mixedBoxCount_eq_weighted (H Z M Y : Finset (𝓞 K)) :
    (mixedBoxCount H Z M Y : ℝ) =
      mixedWeightedRealCount (fun h : H => (h : 𝓞 K)) (fun z : Z => (z : 𝓞 K))
        (fun m : M => (m : 𝓞 K)) (fun y : Y => (y : 𝓞 K))
        (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  simp only [mixedBoxCount,mixedWeightedRealCount,one_mul]
  rw [Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp

theorem mixedBoxCount_le_compactWeightedCount (H Z M Y : Finset (𝓞 K))
    (H₀ P₀ M₀ R₀ : ℝ) (hH₀ : 0 < H₀) (hP₀ : 0 < P₀)
    (hM₀ : 0 < M₀) (hR₀ : 0 < R₀)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ ‖mixedEmbedding K (h : K)‖ ≤ H₀/2)
    (hZ : ∀ z ∈ Z, ‖mixedEmbedding K (z : K)‖ ≤ P₀/2)
    (hM : ∀ m ∈ M, ‖mixedEmbedding K (m : K)‖ ≤ M₀/2)
    (hY : ∀ y ∈ Y, ‖mixedEmbedding K (y : K)‖ ≤ R₀/2) :
    (mixedBoxCount H Z M Y : ℝ) ≤
      compactMixedTransformedWeightedCount (K:=K) nearZeroSchwartz nearZeroSchwartz
        nearZeroSchwartz nearZeroSchwartz nearZeroSchwartz_majorant.2.1
        nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.1
        nearZeroSchwartz_majorant.2.1 H₀ P₀ M₀ R₀ hH₀.ne' hP₀.ne' hM₀.ne' hR₀.ne' := by
  let A := (compactIntegerSupport (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1 H₀ hH₀.ne').erase 0
  let B := compactIntegerSupport (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1 P₀ hP₀.ne'
  let C := compactIntegerSupport (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1 M₀ hM₀.ne'
  let D := compactIntegerSupport (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1 R₀ hR₀.ne'
  let fH : H → A := fun h => ⟨h.val,Finset.mem_erase.mpr
    ⟨(hH h.val h.property).1,nearZero_scaled_mem_support H₀ hH₀ (hH h.val h.property).2⟩⟩
  let fZ : Z → B := fun z => ⟨z.val,nearZero_scaled_mem_support P₀ hP₀ (hZ z.val z.property)⟩
  let fM : M → C := fun m => ⟨m.val,nearZero_scaled_mem_support M₀ hM₀ (hM m.val m.property)⟩
  let fY : Y → D := fun y => ⟨y.val,nearZero_scaled_mem_support R₀ hR₀ (hY y.val y.property)⟩
  let f : H × ((Z × M) × ((Y × Y) × (Y × Y))) → A × ((B × C) × ((D × D) × (D × D))) :=
    Prod.map fH (Prod.map (Prod.map fZ fM) (Prod.map (Prod.map fY fY) (Prod.map fY fY)))
  have hfH : Function.Injective fH := fun x y h => Subtype.ext (congrArg (fun a : A => (a : 𝓞 K)) h)
  have hfZ : Function.Injective fZ := fun x y h => Subtype.ext (congrArg (fun a : B => (a : 𝓞 K)) h)
  have hfM : Function.Injective fM := fun x y h => Subtype.ext (congrArg (fun a : C => (a : 𝓞 K)) h)
  have hfY : Function.Injective fY := fun x y h => Subtype.ext (congrArg (fun a : D => (a : 𝓞 K)) h)
  have hf : Function.Injective f :=
    hfH.prodMap ((hfZ.prodMap hfM).prodMap ((hfY.prodMap hfY).prodMap (hfY.prodMap hfY)))
  let W : A × ((B × C) × ((D × D) × (D × D))) → ℝ := fun t =>
    if mixedWeightedPhase (fun h : A => (h : 𝓞 K)) (fun z : B => (z : 𝓞 K))
      (fun m : C => (m : 𝓞 K)) (fun y : D => (y : 𝓞 K)) t = 0 then
    ‖nearZeroSchwartz (H₀⁻¹ • mixedEmbedding K ((t.1 : 𝓞 K) : K))‖ *
      ((‖nearZeroSchwartz (P₀⁻¹ • mixedEmbedding K ((t.2.1.1 : 𝓞 K) : K))‖ *
        ‖nearZeroSchwartz (M₀⁻¹ • mixedEmbedding K ((t.2.1.2 : 𝓞 K) : K))‖) *
        ((‖nearZeroSchwartz (R₀⁻¹ • mixedEmbedding K ((t.2.2.1.1 : 𝓞 K) : K))‖ *
          ‖nearZeroSchwartz (R₀⁻¹ • mixedEmbedding K ((t.2.2.1.2 : 𝓞 K) : K))‖) *
         (‖nearZeroSchwartz (R₀⁻¹ • mixedEmbedding K ((t.2.2.2.1 : 𝓞 K) : K))‖ *
          ‖nearZeroSchwartz (R₀⁻¹ • mixedEmbedding K ((t.2.2.2.2 : 𝓞 K) : K))‖))) else 0
  have hW : ∀ t, 0 ≤ W t := by intro t; dsimp only [W]; split_ifs <;> positivity
  have hWf (t : H × ((Z × M) × ((Y × Y) × (Y × Y)))) :
      W (f t) = if mixedWeightedPhase (fun h : H => (h : 𝓞 K)) (fun z : Z => (z : 𝓞 K))
        (fun m : M => (m : 𝓞 K)) (fun y : Y => (y : 𝓞 K)) t = 0 then 1 else 0 := by
    dsimp only [W,f,Prod.map,fH,fZ,fM,fY]
    rw [nearZero_scaled_eq_one H₀ hH₀ (hH t.1.val t.1.property).2,
      nearZero_scaled_eq_one P₀ hP₀ (hZ t.2.1.1.val t.2.1.1.property),
      nearZero_scaled_eq_one M₀ hM₀ (hM t.2.1.2.val t.2.1.2.property),
      nearZero_scaled_eq_one R₀ hR₀ (hY t.2.2.1.1.val t.2.2.1.1.property),
      nearZero_scaled_eq_one R₀ hR₀ (hY t.2.2.1.2.val t.2.2.1.2.property),
      nearZero_scaled_eq_one R₀ hR₀ (hY t.2.2.2.1.val t.2.2.2.1.property),
      nearZero_scaled_eq_one R₀ hR₀ (hY t.2.2.2.2.val t.2.2.2.2.property)]
    simp only [norm_one,one_mul]
    rfl
  rw [mixedBoxCount_eq_weighted]
  change mixedWeightedRealCount (fun h : H => (h : 𝓞 K)) (fun z : Z => (z : 𝓞 K))
    (fun m : M => (m : 𝓞 K)) (fun y : Y => (y : 𝓞 K))
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) ≤ ∑ t, W t
  simp only [mixedWeightedRealCount,one_mul]
  simp_rw [← hWf]
  exact sum_comp_le_sum_of_nonneg f hf W hW

#print axioms mixedBoxCount_le_compactWeightedCount
end WaringSiegel.WSL4Local
