import WaringLinear.TraceFibres
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # The real-order moment inequality on the good fibres

The normalized children V_m are m times the shortened sums, with reciprocal
weights w_m=1/m. A bound on the truncated squared samples in each kernel
coset then transfers the pointwise inequality to an integral of the child.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace WaringLinear

theorem good_fibre_jensen {ι : Type*} [Fintype ι]
    (w V H : ι → ℝ) (x p : ℝ) (hp : 1≤p) (hx : 0≤x)
    (hw : ∀ i, 0≤w i) (hV : ∀ i, 0≤V i)
    (hm : (∑ i, w i)≤1) (hparent : x≤∑ i, w i*V i)
    (hgood : ∀ i, x≤2*H i) :
    x^(p+2) ≤ ∑ i, 4*w i*(V i)^p*(H i)^2 := by
  have hz : p≠0 := by linarith
  have hj := (convexOn_rpow hp).map_add_sum_le (t := Finset.univ)
    (w := w) (p := V) (q := (0:ℝ)) (v := 1-∑ i, w i)
    (fun i _ => hw i) (by ring) (fun i _ => hV i) (sub_nonneg.mpr hm) (by simp)
  simp only [smul_eq_mul,mul_zero,zero_add,Real.zero_rpow hz] at hj
  have hxJ := (Real.rpow_le_rpow hx hparent (by linarith : 0≤p)).trans hj
  have hid : x^(p+2)=x^p*x^2 := by
    by_cases h : x=0
    · simp [h,Real.zero_rpow hz,Real.zero_rpow (show p+2≠0 by linarith)]
    · rw [Real.rpow_add (lt_of_le_of_ne hx (Ne.symm h)),Real.rpow_two]
  rw [hid]
  calc
    _ ≤ (∑ i, w i*(V i)^p)*x^2 := mul_le_mul_of_nonneg_right hxJ (sq_nonneg _)
    _ = ∑ i, w i*(V i)^p*x^2 := Finset.sum_mul _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := pow_le_pow_left₀ hx (hgood i) 2
      have hi' := mul_le_mul_of_nonneg_left hi (mul_nonneg (hw i) (Real.rpow_nonneg (hV i) p))
      nlinarith only [hi']

variable {T : Type*} [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]

/-- A nonnegative weight of bounded sum in each fibre can be applied to an
arbitrary nonnegative child function pulled back by the quotient. -/
theorem integral_fibre_weight_bound (μ : Measure T) [μ.IsAddRightInvariant]
    (π : T →+ T) (hπ : MeasurePreserving π μ μ) [Fintype π.ker]
    (u g : T → ℝ) (B : ℝ) (hg : Integrable g μ) (hpos : ∀ x, 0≤g x)
    (hi : Integrable (fun x => u x*g (π x)) μ)
    (hfib : ∀ x, (∑ η : π.ker, u (x+η.1))≤B) :
    (∫ x, u x*g (π x) ∂μ) ≤ B/Fintype.card π.ker*(∫ y, g y ∂μ) := by
  let G : T → ℝ := fun x => g (π x)
  have hG : Integrable G μ := hπ.integrable_comp_of_integrable hg
  have hinv (η : π.ker) (x : T) : G (x+η.1)=G x := by
    simp [G,AddMonoidHom.mem_ker.mp η.property]
  have havg := WaringSiegel.WSL2.integral_finite_translation_average_mul μ
    (fun η : π.ker => (η:T)) u G hi hinv
  have havgi := WaringSiegel.WSL2.integrable_finite_translation_average_mul μ
    (fun η : π.ker => (η:T)) u G hi hinv
  have hpoint (x : T) : (𝔼 η : π.ker, u (x+η.1)) ≤ B/Fintype.card π.ker := by
    rw [Fintype.expect_eq_sum_div_card]
    exact div_le_div_of_nonneg_right (hfib x) (Nat.cast_nonneg _)
  have hpush : (∫ x, G x ∂μ)=∫ y, g y ∂μ := by
    unfold G
    rw [← integral_map hπ.measurable.aemeasurable
      (by simpa only [hπ.map_eq] using hg.aestronglyMeasurable),hπ.map_eq]
  calc
    _ = _ := havg.symm
    _ ≤ ∫ x, (B/Fintype.card π.ker)*G x ∂μ :=
      integral_mono havgi (hG.const_mul _) (fun x =>
        mul_le_mul_of_nonneg_right (hpoint x) (hpos (π x)))
    _ = _ := by rw [integral_const_mul,hpush]

/-- The integrated good-set inequality at a real moment order p+2.
The finite cover may vary with the selected marked product. -/
theorem integrate_good_fibre {ι : Type*} [Fintype ι]
    (μ : Measure T) [μ.IsAddRightInvariant] (G : Set T)
    (π : ι → T →+ T) (hπ : ∀ i, MeasurePreserving (π i) μ μ)
    [∀ i, Fintype (π i).ker] (w B : ι → ℝ) (F : T → ℝ)
    (V H : ι → T → ℝ) (p : ℝ) (hp : 1≤p)
    (hw : ∀ i, 0≤w i) (hm : (∑ i, w i)≤1)
    (hF : ∀ x, 0≤F x) (hV : ∀ i x, 0≤V i x)
    (hparent : ∀ x ∈ G, F x≤∑ i, w i*V i (π i x))
    (hgood : ∀ x ∈ G, ∀ i, F x≤2*H i x)
    (hIntF : Integrable (G.indicator (fun x => (F x)^(p+2))) μ)
    (hIntV : ∀ i, Integrable (fun x => (V i x)^p) μ)
    (hIntVH : ∀ i, Integrable (fun x =>
      G.indicator (fun z => (H i z)^2) x*(V i (π i x))^p) μ)
    (hfib : ∀ i x, (∑ η : (π i).ker, G.indicator (fun z => (H i z)^2) (x+η.1))≤B i) :
    (∫ x, G.indicator (fun z => (F z)^(p+2)) x ∂μ) ≤
      ∑ i, 4*w i*(B i/Fintype.card (π i).ker)*(∫ y, (V i y)^p ∂μ) := by
  classical
  let W (i : ι) (x : T) := G.indicator (fun z => (H i z)^2) x * (V i (π i x))^p
  have hI (i : ι) : Integrable (fun x => (4*w i)*W i x) μ := (hIntVH i).const_mul _
  have hpoint (x : T) : G.indicator (fun z => (F z)^(p+2)) x ≤ ∑ i, (4*w i)*W i x := by
    by_cases hx : x∈G
    · simp only [W,Set.indicator_of_mem hx]
      simpa only [mul_assoc,mul_left_comm,mul_comm] using
        good_fibre_jensen w (fun i => V i (π i x)) (fun i => H i x) (F x) p hp (hF x)
          hw (fun i => hV i _) hm (hparent x hx) (hgood x hx)
    · simp [hx,W]
  calc
    _ ≤ ∫ x, (∑ i, (4*w i)*W i x) ∂μ :=
      integral_mono hIntF (integrable_finset_sum _ (fun i _ => hI i)) hpoint
    _ = ∑ i, (4*w i)*(∫ x, W i x ∂μ) := by
      rw [integral_finset_sum _ (fun i _ => hI i)]
      simp only [integral_const_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := integral_fibre_weight_bound μ (π i) (hπ i)
        (G.indicator (fun z => (H i z)^2)) (fun y => (V i y)^p) (B i) (hIntV i)
        (fun y => Real.rpow_nonneg (hV i y) _) (hIntVH i) (hfib i)
      simpa only [W,mul_assoc] using mul_le_mul_of_nonneg_left hi
        (mul_nonneg (by norm_num : (0:ℝ)≤4) (hw i))

#print axioms good_fibre_jensen
#print axioms integral_fibre_weight_bound
#print axioms integrate_good_fibre
end WaringLinear
