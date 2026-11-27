import WaringLinear.GoodFibreMoment
import WaringLinear.ShortenedMoment

/-! # Integrating the three branches of a Fourier moment stage

The actual torus norm of a parent is controlled by the lower moment, the
contracted moments on the good fibres, and the same-order children
selected by inclusion--exclusion. All constants and kernel degrees are
retained explicitly.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace WaringLinear
section
variable {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T] in
/-- Pointwise small/good/exceptional splitting at arbitrary real order. -/
theorem stage_majorant (G : Set T) (F : T → ℝ) (J : κ → T → ℝ)
    (X p h z D : ℝ) (hX : 0<X) (hp : 1≤p) (hh : 0<h) (hhp : h<p+2) (hD : 0≤D)
    (hF : ∀ x,0≤F x) (hJ : ∀ j x,0≤J j x)
    (hsplit : ∀ x, x∉G → F x≤X^(1-z) ∨ ∃ j,F x≤D*J j x) (x : T) :
    (F x)^(p+2) ≤ X^((1-z)*(p+2-h))*(F x)^h+
      G.indicator (fun u => (F u)^(p+2)) x + D^(p+2)*∑ j,(J j x)^(p+2) := by
  have hp' : 0≤p+2 := by linarith
  have hL : 0≤X^((1-z)*(p+2-h))*(F x)^h :=
    mul_nonneg (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg (hF x) _)
  have hS : 0≤D^(p+2)*∑ j,(J j x)^(p+2) :=
    mul_nonneg (Real.rpow_nonneg hD _) (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hJ j x) _))
  by_cases hx : x∈G
  · rw [Set.indicator_of_mem hx]
    linarith
  · rw [Set.indicator_of_notMem hx,add_zero]
    rcases hsplit x hx with hl|⟨j,hj⟩
    · exact (small_spectrum_pointwise _ _ _ _ _ (hF x) hX hh hhp hl).trans (le_add_of_nonneg_right hS)
    · have hhj := Real.rpow_le_rpow (hF x) hj hp'
      rw [Real.mul_rpow hD (hJ j x)] at hhj
      have ht : (J j x)^(p+2)≤∑ i,(J i x)^(p+2) := Finset.single_le_sum
        (fun i _ => Real.rpow_nonneg (hJ i x) _) (Finset.mem_univ j)
      exact (hhj.trans (mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hD _))).trans
        (le_add_of_nonneg_left hL)

/-- The exact integrated estimate on an additive torus. V is the
normalized child magnitude and J the pulled-back exceptional children.
The index of the good fibres appears as the actual kernel cardinality. -/
theorem integrate_fourier_stage (μ : Measure T) [μ.IsAddRightInvariant]
    (G : Set T) (π : ι → T →+ T) (hπ : ∀ i, MeasurePreserving (π i) μ μ)
    [∀ i, Fintype (π i).ker] (w B : ι → ℝ)
    (F : T → ℝ) (V H : ι → T → ℝ) (J : κ → T → ℝ)
    (X p h z D : ℝ) (hX : 0<X) (hp : 1≤p) (hh : 0<h) (hhp : h<p+2) (hD : 0≤D)
    (hw : ∀ i,0≤w i) (hm : (∑i,w i)≤1)
    (hF : ∀ x,0≤F x) (hV : ∀ i x,0≤V i x) (hJ : ∀ j x,0≤J j x)
    (hparent : ∀ x∈G,F x≤∑ i,w i*V i (π i x))
    (hgood : ∀ x∈G,∀ i,F x≤2*H i x)
    (hsplit : ∀ x,x∉G → F x≤X^(1-z) ∨ ∃ j,F x≤D*J j x)
    (hInt : Integrable (fun x => (F x)^(p+2)) μ)
    (hIntFG : Integrable (G.indicator (fun x => (F x)^(p+2))) μ)
    (hIntLow : Integrable (fun x => (F x)^h) μ)
    (hIntV : ∀ i, Integrable (fun x => (V i x)^p) μ)
    (hIntJ : ∀ j, Integrable (fun x => (J j x)^(p+2)) μ)
    (hIntVH : ∀ i, Integrable (fun x => G.indicator (fun u => (H i u)^2) x*(V i (π i x))^p) μ)
    (hfib : ∀ i x,(∑ η : (π i).ker,G.indicator (fun u => (H i u)^2) (x+η.1))≤B i) :
    (∫x,(F x)^(p+2) ∂μ) ≤ X^((1-z)*(p+2-h))*(∫x,(F x)^h ∂μ)+
      (∑ i,4*w i*(B i/Fintype.card (π i).ker)*(∫x,(V i x)^p ∂μ))+
      D^(p+2)*∑ j,∫x,(J j x)^(p+2) ∂μ := by
  have h1 := (hIntLow.const_mul (X^((1-z)*(p+2-h)))).add hIntFG
  have h2 := (integrable_finset_sum (Finset.univ : Finset κ) (fun j _ => hIntJ j)).const_mul (D^(p+2))
  have hb := integral_mono hInt (h1.add h2)
    (stage_majorant G F J X p h z D hX hp hh hhp hD hF hJ hsplit)
  change Integrable (fun x => X^((1-z)*(p+2-h))*(F x)^h+G.indicator (fun u => (F u)^(p+2)) x) μ at h1
  simp only [Pi.add_apply] at hb
  rw [integral_add h1 h2,integral_add (hIntLow.const_mul _) hIntFG,
    integral_const_mul,integral_const_mul,integral_finset_sum _ (fun j _ => hIntJ j)] at hb
  have hG := integrate_good_fibre μ G π hπ w B F V H p hp hw hm hF hV
    hparent hgood hIntFG hIntV hIntVH hfib
  linarith only [hb,hG]

end
#print axioms integrate_fourier_stage
end WaringLinear
