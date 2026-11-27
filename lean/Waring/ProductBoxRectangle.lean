import Waring.ProductBoxDistribution

/-! # A positive-measure rectangle for the mixed real density -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox

def intervalBox (L : ℕ) (a b : ℝ) : Set (Fin L → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc a b)

theorem measurableSet_intervalBox (L : ℕ) (a b : ℝ) : MeasurableSet (intervalBox L a b) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)

theorem mem_intervalBox {L : ℕ} {a b : ℝ} {x : Fin L → ℝ} :
    x∈intervalBox L a b ↔ ∀ i,x i∈Set.Icc a b := by
  simp only [intervalBox,Set.mem_pi,Set.mem_univ,true_imp_iff]

theorem unitIntervalMeasure_Icc {a b : ℝ} (ha : 0≤a) (hb : b≤1) :
    unitIntervalMeasure (Set.Icc a b)=ENNReal.ofReal (b-a) := by
  unfold unitIntervalMeasure
  rw [Measure.restrict_apply measurableSet_Icc,
    Set.inter_eq_left.mpr (Set.Icc_subset_Icc ha hb),Real.volume_Icc]

theorem boxMeasure_intervalBox (L : ℕ) {a b : ℝ} (ha : 0≤a) (hb : b≤1) :
    boxMeasure L (intervalBox L a b)=ENNReal.ofReal (b-a)^L := by
  simp only [boxMeasure,intervalBox,Measure.pi_pi,unitIntervalMeasure_Icc ha hb,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

def mixedRectangle (u v L : ℕ) (a b : ℝ) : Set (MixedSpace u v L) :=
  (intervalBox u a b)×ˢ(Set.univ.pi (fun _ : Fin v => intervalBox L a b))

theorem measurableSet_mixedRectangle (u v L : ℕ) (a b : ℝ) :
    MeasurableSet (mixedRectangle u v L a b) :=
  (measurableSet_intervalBox u a b).prod
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_intervalBox L a b))

theorem mixedRectangle_measure_pos (u v L : ℕ) {a b : ℝ}
    (ha : 0≤a) (hab : a<b) (hb : b≤1) :
    0<(mixedMeasure u v L).real (mixedRectangle u v L a b) := by
  apply ENNReal.toReal_pos
  · unfold mixedMeasure mixedRectangle productBlocksMeasure
    rw [Measure.prod_prod,Measure.pi_pi]
    simp only [boxMeasure_intervalBox _ ha hb,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
    have hn := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
    exact mul_ne_zero (pow_ne_zero _ hn) (pow_ne_zero _ (pow_ne_zero _ hn))
  · exact measure_ne_top _ _

theorem product_interval_upper {L : ℕ} {a b : ℝ} (ha : 0≤a) (hb : b≤1)
    {x : Fin (L+1) → ℝ} (hx : x∈intervalBox (L+1) a b) :
    0≤∏ i,x i ∧ (∏ i,x i)≤b := by
  have hx' := mem_intervalBox.mp hx
  have hx0 (i : Fin (L+1)) : 0≤x i := ha.trans (hx' i).1
  refine ⟨Finset.prod_nonneg (fun i _ => hx0 i),?_⟩
  rw [Fin.prod_univ_succ]
  have hprod : (∏ i : Fin L,x i.succ)≤1 :=
    Finset.prod_le_one (fun i _ => hx0 _) (fun i _ => (hx' _).2.trans hb)
  exact (mul_le_mul_of_nonneg_left hprod (hx0 0)).trans (by simpa using (hx' 0).2)

theorem mixedValue_rectangle_bounds (k u v L : ℕ) (hu : 1≤u) {a b : ℝ}
    (ha : 0≤a) (hb : b≤1) {z : MixedSpace u v (L+1)}
    (hz : z∈mixedRectangle u v (L+1) a b) :
    a^k≤mixedValue k u v (L+1) z ∧
      mixedValue k u v (L+1) z≤((u : ℝ)+v)*b^k := by
  have hx := mem_intervalBox.mp hz.1
  have hy (j : Fin v) : z.2 j∈intervalBox (L+1) a b := hz.2 j (Set.mem_univ j)
  have hx0 (i : Fin u) : 0≤z.1 i := ha.trans (hx i).1
  have hp (j : Fin v) := product_interval_upper ha hb (hy j)
  have hprod0 : 0≤∑ j,(∏ i,z.2 j i)^k :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (hp j).1 _)
  have hordinary : a^k≤∑ i,z.1 i^k := by
    let i : Fin u := ⟨0,by omega⟩
    exact (pow_le_pow_left₀ ha (hx i).1 k).trans
      (Finset.single_le_sum (fun j _ => pow_nonneg (hx0 j) _) (Finset.mem_univ i))
  constructor
  · unfold mixedValue
    linarith
  · unfold mixedValue
    calc
      _ ≤ (∑ _i : Fin u,b^k)+∑ _j : Fin v,b^k := by
        apply add_le_add
        · exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (hx0 i) (hx i).2 k)
        · exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (hp j).1 (hp j).2 k)
      _ = _ := by simp; ring

#print axioms mixedRectangle_measure_pos
#print axioms mixedValue_rectangle_bounds
end Waring.ProductBox
