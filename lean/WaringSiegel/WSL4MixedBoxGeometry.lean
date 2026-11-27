import WaringSiegel.WSL4MixedOffdiagonal
import WaringSiegel.WSL4MixedCountIntegral

/-! # Explicit rescaling of the original mixed boxes into the fixed smooth majorant -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def mixedShiftBox (X A : Finset (𝓞 K)) : Finset (𝓞 K) :=
  ((A.product (X.product X)).filter (fun t => t.2.1≠t.2.2 ∧ t.1^3 ∣ t.2.2-t.2.1)).image
    (fun t => cubicCongruenceQuotient t.1 t.2.1 t.2.2)

def mixedSumBox (X : Finset (𝓞 K)) : Finset (𝓞 K) :=
  (X.product X).image (fun t => t.1+t.2)

theorem mixedShiftBox_bounds (X A : Finset (𝓞 K)) (P M : ℝ) (hM : 0 < M)
    (hX : ∀ x ∈ X, ‖mixedEmbedding K (x : K)‖ ≤ P)
    (hA : ∀ m ∈ A, ∀ v : InfinitePlace K, M ≤ v (m : K)) :
    ∀ h ∈ mixedShiftBox X A, h ≠ 0 ∧ ‖mixedEmbedding K (h : K)‖ ≤ 2*P/M^3 := by
  intro h hh
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨htmem,hneq,hdiv⟩ := Finset.mem_filter.mp ht
  obtain ⟨hm,hxy⟩ := Finset.mem_product.mp htmem
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  refine ⟨cubicCongruenceQuotient_ne_zero _ _ _ hdiv hneq,?_⟩
  apply (mixed_norm_le_iff _ _).mpr
  intro v
  rw [normAtPlace_apply]
  exact cubicCongruenceQuotient_place_bound t.1 t.2.1 t.2.2 hdiv P M hM (hA _ hm)
    (fun v => by rw [← normAtPlace_apply]; exact (normAtPlace_le_mixed_norm _ v).trans (hX _ hx))
    (fun v => by rw [← normAtPlace_apply]; exact (normAtPlace_le_mixed_norm _ v).trans (hX _ hy)) v

theorem mixedSumBox_bounds (X : Finset (𝓞 K)) (P : ℝ)
    (hX : ∀ x ∈ X, ‖mixedEmbedding K (x : K)‖ ≤ P) :
    ∀ z ∈ mixedSumBox X, ‖mixedEmbedding K (z : K)‖ ≤ 2*P := by
  intro z hz
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
  change ‖mixedEmbedding K ((t.1:K)+(t.2:K))‖≤2*P
  rw [map_add]
  exact (norm_add_le _ _).trans (by
    have hx := hX t.1 (Finset.mem_product.mp ht).1
    have hy := hX t.2 (Finset.mem_product.mp ht).2
    linarith)

theorem mixedCongruentOffdiagonalCount_le_shiftBox (X A Y : Finset (𝓞 K))
    (hA : ∀ m ∈ A, m ≠ 0) :
    mixedCongruentOffdiagonalCount X A Y ≤ mixedBoxCount (mixedShiftBox X A) (mixedSumBox X) A Y := by
  apply mixedCongruentOffdiagonalCount_le X A Y (mixedShiftBox X A) (mixedSumBox X) hA
  · intro m hm x hx y hy hneq hdiv
    exact Finset.mem_image.mpr ⟨(m,(x,y)),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hm,Finset.mem_product.mpr ⟨hx,hy⟩⟩,hneq,hdiv⟩,rfl⟩
  · intro x hx y hy
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩

theorem mixed_offdiagonal_le_rescaled_integral (X A Y : Finset (𝓞 K))
    (P M : ℝ) (hP : 0 < P) (hM : 0 < M)
    (hX : ∀ x ∈ X, ‖mixedEmbedding K (x : K)‖ ≤ P)
    (hAlo : ∀ m ∈ A, ∀ v : InfinitePlace K, M ≤ v (m : K))
    (hAhi : ∀ m ∈ A, ‖mixedEmbedding K (m : K)‖ ≤ 2*M)
    (hY : ∀ y ∈ Y, ‖mixedEmbedding K (y : K)‖ ≤ P/M) :
    (mixedCongruentOffdiagonalCount X A Y : ℝ) ≤
      ‖∫ q, nearZeroMixedSIntegrand (K:=K) (((4 : ℝ)^7*P)/(4*M)^3)
        ((4 : ℝ)^7*P) (4*M) (((4 : ℝ)^7*P)/(4*M))
        (by positivity) (by positivity) (by positivity) (by positivity) q ∂traceHaar‖ := by
  have hA0 : ∀ m ∈ A, m ≠ 0 := by
    intro m hm hz
    let v : InfinitePlace K := Classical.choice inferInstance
    have hh := hAlo m hm v
    have hh' : M≤0 := by simpa [hz] using hh
    linarith
  have hc : (mixedCongruentOffdiagonalCount X A Y : ℝ) ≤
      mixedBoxCount (mixedShiftBox X A) (mixedSumBox X) A Y := by
    exact_mod_cast mixedCongruentOffdiagonalCount_le_shiftBox X A Y hA0
  apply hc.trans
  apply mixedBoxCount_le_nearZero_integral_norm
    (mixedShiftBox X A) (mixedSumBox X) A Y
    (((4 : ℝ)^7*P)/(4*M)^3) ((4 : ℝ)^7*P) (4*M) (((4 : ℝ)^7*P)/(4*M))
    (by positivity) (by positivity) (by positivity) (by positivity)
  · intro h hh
    obtain ⟨hn,hb⟩ := mixedShiftBox_bounds X A P M hM hX hAlo h hh
    refine ⟨hn,hb.trans ?_⟩
    have he : (((4 : ℝ)^7*P)/(4*M)^3)/2 = 128*P/M^3 := by field_simp <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  · intro z hz
    apply (mixedSumBox_bounds X P hX z hz).trans
    norm_num
    linarith
  · intro m hm
    linarith [hAhi m hm]
  · intro y hy
    apply (hY y hy).trans
    have he : (((4 : ℝ)^7*P)/(4*M))/2 = 2048*(P/M) := by field_simp <;> ring
    rw [he]
    have hPM : 0 < P/M := div_pos hP hM
    linarith

#print axioms mixed_offdiagonal_le_rescaled_integral
end WaringSiegel.WSL4Local
