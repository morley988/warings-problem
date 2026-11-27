import Waring.ProductMultiplicity
import Waring.SourcePhaseConstants
import Waring.CoefficientPower

/-!
# Actual Cartesian shift averages and padded product sampling

The positive tuple box has volume exactly the product of its coordinate
bounds. Product grouping is proved using the divisor multiplicity theorem.
A padded sampled cutoff J is allowed, with the explicit loss J/volume
bounded by Cpad. The distinguished coefficient coordinate is retained
outside the product and the sampled integer range starts at one (sigma=1).
-/

noncomputable section
open scoped BigOperators
namespace Waring.CartesianProductSampling
open ProductMultiplicity FiniteResourceHolder CoefficientFactorization

def positiveBox {r : ℕ} (bounds : Fin r → ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc 1 (bounds i))

theorem mem_positiveBox {r : ℕ} {bounds x : Fin r → ℕ} :
    x ∈ positiveBox bounds ↔ ∀ i, 1 ≤ x i ∧ x i ≤ bounds i := by
  simp only [positiveBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem positiveBox_card {r : ℕ} (bounds : Fin r → ℕ) :
    (positiveBox bounds).card = tupleProduct bounds := by
  simp [positiveBox, Fintype.card_piFinset, tupleProduct, Nat.card_Icc]

theorem tupleProduct_pos {r : ℕ} (bounds : Fin r → ℕ) (hb : ∀ i, 0 < bounds i) :
    0 < tupleProduct bounds := Finset.prod_pos (fun i _ => hb i)

theorem positiveBox_product_range {r : ℕ} (bounds : Fin r → ℕ)
    (x : Fin r → ℕ) (hx : x ∈ positiveBox bounds) :
    tupleProduct x ∈ Finset.Icc 1 (tupleProduct bounds) :=
  coordinate_bounds_product_range x bounds
    (fun i => (mem_positiveBox.mp hx i).1) (fun i => (mem_positiveBox.mp hx i).2)

theorem average_positiveBox {r : ℕ} (bounds : Fin r → ℕ) (F : (Fin r → ℕ) → ℝ) :
    average (fun x : positiveBox bounds => F x) =
      (∑ x ∈ positiveBox bounds, F x)/(tupleProduct bounds:ℝ) := by
  unfold average
  rw [Fintype.card_coe, positiveBox_card]
  congr 1
  exact Finset.sum_attach _ F

/-- The head coordinate and all remaining coordinates are regrouped exactly. -/
theorem positiveBox_sum_head_tail {r : ℕ} (bounds : Fin (r+1) → ℕ)
    (F : ℕ → (Fin r → ℕ) → ℝ) :
    (∑ x ∈ positiveBox bounds, F (x 0) (fun i => x i.succ)) =
      ∑ h ∈ Finset.Icc 1 (bounds 0),
        ∑ y ∈ positiveBox (fun i => bounds i.succ), F h y := by
  classical
  rw [← Finset.sum_product (s:=Finset.Icc 1 (bounds 0))
    (t:=positiveBox (fun i => bounds i.succ)) (f:=fun hy => F hy.1 hy.2)]
  apply Finset.sum_bij (fun x _ => (x 0, fun i => x i.succ))
  · intro x hx
    have hh := mem_positiveBox.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hh 0), mem_positiveBox.mpr (fun i => hh i.succ)⟩
  · intro x hx y hy hxy
    have h0 := congrArg Prod.fst hxy
    have ht := congrArg Prod.snd hxy
    funext i
    refine Fin.cases h0 (fun i => ?_) i
    exact congrFun ht i
  · intro y hy
    rcases Finset.mem_product.mp hy with ⟨hh,ht⟩
    refine ⟨Fin.cons y.1 y.2, mem_positiveBox.mpr ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using Finset.mem_Icc.mp hh
      · simpa using mem_positiveBox.mp ht i
    · simp
  · intro x hx
    rfl

/-- Any coefficient coordinate may be moved to the distinguished position
by a finite permutation; the Cartesian sum is unchanged. -/
theorem positiveBox_reindex {r : ℕ} (e : Fin r ≃ Fin r) (bounds : Fin r → ℕ)
    (F : (Fin r → ℕ) → ℝ) :
    (∑ x ∈ positiveBox bounds, F x) =
      ∑ y ∈ positiveBox (fun i => bounds (e i)), F (fun i => y (e.symm i)) := by
  classical
  apply Finset.sum_bij (fun x _ i => x (e i))
  · intro x hx
    exact mem_positiveBox.mpr (fun i => mem_positiveBox.mp hx (e i))
  · intro x hx y hy hxy
    funext i
    have hh := congrFun hxy (e.symm i)
    simpa only [e.apply_symm_apply] using hh
  · intro y hy
    refine ⟨fun i => y (e.symm i), mem_positiveBox.mpr ?_, ?_⟩
    · intro i
      simpa only [e.apply_symm_apply] using mem_positiveBox.mp hy (e.symm i)
    · funext i
      simp only [e.symm_apply_apply]
  · intro x hx
    simp only [e.apply_symm_apply]

theorem sum_Icc_one_eq_range (J : ℕ) (F : ℕ → ℝ) :
    (∑ z ∈ Finset.Icc 1 J, F z) = ∑ j ∈ Finset.range J, F (j+1) := by
  apply Finset.sum_bij (fun z _ => z-1)
  · intro z hz
    have hh := Finset.mem_Icc.mp hz
    apply Finset.mem_range.mpr
    omega
  · intro z hz w hw heq
    have hz' := (Finset.mem_Icc.mp hz).1
    have hw' := (Finset.mem_Icc.mp hw).1
    omega
  · intro j hj
    refine ⟨j+1, Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hj; omega⟩,by omega⟩
  · intro z hz
    have hz' := (Finset.mem_Icc.mp hz).1
    congr 1
    omega

/-- Grouping an actual Cartesian average into a padded sampled average.
The ratio between the padded and actual volumes is kept explicit. -/
theorem padded_product_average (r : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : ℝ, 1 ≤ P → ∀ bounds : Fin r → ℕ,
      (∀ i, 0 < bounds i) → ∀ J : ℕ, tupleProduct bounds ≤ J → (J:ℝ) ≤ P^B →
      ∀ Cpad : ℝ, (J:ℝ) ≤ Cpad*(tupleProduct bounds:ℝ) →
      ∀ F : ℕ → ℝ, (∀ z ∈ Finset.Icc 1 J, 0 ≤ F z) →
      (∑ x ∈ positiveBox bounds, F (tupleProduct x))/(tupleProduct bounds:ℝ) ≤
        D*Cpad*P^ε*((∑ z ∈ Finset.Icc 1 J, F z)/(J:ℝ)) := by
  obtain ⟨D,hD,hgroup⟩ := weighted_product_grouping_polynomial r hB hε
  refine ⟨D,hD,?_⟩
  intro P hP bounds hb J hVJ hJP Cpad hpad F hF
  have hV : 0 < tupleProduct bounds := tupleProduct_pos bounds hb
  have hJ : 0 < J := hV.trans_le hVJ
  have hVR : 0 < (tupleProduct bounds:ℝ) := by exact_mod_cast hV
  have hJR : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hnon : 0 ≤ ∑ z ∈ Finset.Icc 1 J, F z := Finset.sum_nonneg hF
  have HH := hgroup P hP J hJ hJP (positiveBox bounds) F
    (by
      intro x hx
      have hr := Finset.mem_Icc.mp (positiveBox_product_range bounds x hx)
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.trans hVJ⟩) hF
  calc
    _ ≤ (D*P^ε*(∑ z ∈ Finset.Icc 1 J, F z))/(tupleProduct bounds:ℝ) :=
      div_le_div_of_nonneg_right HH hVR.le
    _ = (D*P^ε*((∑ z ∈ Finset.Icc 1 J, F z)/(J:ℝ)))*((J:ℝ)/(tupleProduct bounds:ℝ)) := by
      field_simp
    _ ≤ (D*P^ε*((∑ z ∈ Finset.Icc 1 J, F z)/(J:ℝ)))*Cpad :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ hVR).mpr hpad)
        (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hP) _))
          (div_nonneg hnon hJR.le))
    _ = _ := by ring

/-- Coefficient sampling retains the distinguished h coordinate. The other
coordinates are grouped using the same uniform divisor constant for every h. -/
theorem padded_distinguished_average (r : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : ℝ, 1 ≤ P → ∀ H : ℕ, 0 < H →
      ∀ bounds : Fin r → ℕ, (∀ i, 0 < bounds i) →
      ∀ J : ℕ, tupleProduct bounds ≤ J → (J:ℝ) ≤ P^B →
      ∀ Cpad : ℝ, (J:ℝ) ≤ Cpad*(tupleProduct bounds:ℝ) →
      ∀ F : ℕ → ℕ → ℝ,
      (∀ h ∈ Finset.Icc 1 H, ∀ z ∈ Finset.Icc 1 J, 0 ≤ F h z) →
      (∑ h ∈ Finset.Icc 1 H, ∑ x ∈ positiveBox bounds, F h (tupleProduct x))/
        ((H:ℝ)*(tupleProduct bounds:ℝ)) ≤
      D*Cpad*P^ε*((∑ h ∈ Finset.Icc 1 H, ∑ z ∈ Finset.Icc 1 J, F h z)/((H:ℝ)*J)) := by
  obtain ⟨D,hD,hgroup⟩ := padded_product_average r hB hε
  refine ⟨D,hD,?_⟩
  intro P hP H hH bounds hb J hVJ hJP Cpad hpad F hF
  have hHR : 0 < (H:ℝ) := by exact_mod_cast hH
  have HH := Finset.sum_le_sum (fun h hh => hgroup P hP bounds hb J hVJ hJP Cpad hpad (F h) (hF h hh))
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_div] at HH
  have HD := div_le_div_of_nonneg_right HH hHR.le
  convert HD using 1 <;> ring

/-- The full tuple box, with its first coordinate distinguished, has the
same average as the preceding nested form. -/
theorem fullbox_distinguished_average {r : ℕ} (bounds : Fin (r+1) → ℕ)
    (F : ℕ → ℕ → ℝ) :
    (∑ x ∈ positiveBox bounds, F (x 0) (tupleProduct (fun i => x i.succ)))/
      (tupleProduct bounds:ℝ) =
    (∑ h ∈ Finset.Icc 1 (bounds 0),
      ∑ y ∈ positiveBox (fun i => bounds i.succ), F h (tupleProduct y))/
      ((bounds 0:ℝ)*(tupleProduct (fun i => bounds i.succ):ℝ)) := by
  rw [positiveBox_sum_head_tail bounds (fun h y => F h (tupleProduct y))]
  simp only [tupleProduct, Fin.prod_univ_succ, Nat.cast_mul]

/-- Exact sigma=1 bridge to the actual coefficient sampling operator. -/
theorem coefficient_sample_Icc_eq (C : Finset ℕ) (degree power M H J : ℕ)
    (hC : ∀ m ∈ C, m ≤ M) (β : ℝ) :
    (∑ h ∈ Finset.Icc 1 H, ∑ z ∈ Finset.Icc 1 J,
      ‖CoefficientPower.coefficientWeyl C degree (β*(h:ℝ)^3*(z:ℝ))‖^(2*power)) =
      CubicCoefficientSampling.cubicSecondMoment β H
        (CoefficientPower.supportLength degree power M) J
        (CoefficientPower.powerCoefficient C degree power) (fun _ => 1) := by
  calc
    _ = ∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
        ‖CoefficientPower.coefficientWeyl C degree (β*(h:ℝ)^3*((j:ℝ)+1))‖^(2*power) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [sum_Icc_one_eq_range]
      simp only [Nat.cast_add, Nat.cast_one]
    _ = _ := CoefficientPower.sampled_power_eq_cubicSecondMoment C degree power M H J hC β (fun _ => 1)

#print axioms padded_product_average
#print axioms padded_distinguished_average
#print axioms fullbox_distinguished_average
#print axioms coefficient_sample_Icc_eq

end Waring.CartesianProductSampling
