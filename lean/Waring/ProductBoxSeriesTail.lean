import Waring.ProductBoxModelSum

/-! # Uniform finite truncation of the actual arithmetic singular series -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace Waring.ProductBox
open EndgameCompletion RestrictedSmoothArcs

def natSeriesTail (b : ℕ → ℝ) (N : ℕ) : ℝ := ∑' j : ℕ,b (j+N)

theorem natSeriesTail_tendsto_zero {b : ℕ → ℝ} (hb : Summable b) :
    Tendsto (natSeriesTail b) atTop (𝓝 0) := by
  have he (N : ℕ) : natSeriesTail b N=(∑' j : ℕ,b j)-∑ j∈Finset.range N,b j := by
    have hh := hb.sum_add_tsum_nat_add N
    change (∑ j∈Finset.range N,b j)+natSeriesTail b N=(∑' j : ℕ,b j) at hh
    linarith
  simp_rw [show natSeriesTail b=(fun N => (∑' j : ℕ,b j)-∑ j∈Finset.range N,b j) from funext he]
  simpa only [sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑' j : ℕ,b j) atTop (𝓝 (∑' j : ℕ,b j))).sub
      hb.hasSum.tendsto_sum_nat

theorem complex_series_tail_bound {f : ℕ → ℂ} {b : ℕ → ℝ}
    (hb : Summable b) (hbound : ∀ q,‖f q‖≤b q) (N : ℕ) :
    ‖(∑' q : ℕ,f q)-∑ q∈Finset.range N,f q‖≤natSeriesTail b N := by
  have hs : Summable (fun q => ‖f q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hb
  have hinj : Function.Injective (fun j : ℕ => j+N) := fun _ _ hh => Nat.add_right_cancel hh
  have hh := hs.of_norm.sum_add_tsum_nat_add N
  rw [← hh,add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm (hs.comp_injective hinj)).trans
    (tsum_le_tsum (fun j => hbound _) (hs.comp_injective hinj) (hb.comp_injective hinj))

theorem broadDenominators_sum_eq_range (f : ℕ → ℂ) (hf0 : f 0=0) (N : ℕ) :
    (∑ q∈broadDenominators ((N-1 : ℕ) : ℝ),f (q : ℕ))=∑ q∈Finset.range N,f q := by
  classical
  unfold broadDenominators
  simp only [Nat.floor_natCast]
  have hs : (∑ q∈(Finset.Icc 1 (N-1)).subtype (fun q : ℕ => 0<q),f q.val)=
      ∑ q∈Finset.Icc 1 (N-1),f q := by
    apply Finset.sum_bij (fun q _ => q.val)
    · intro q hq
      exact Finset.mem_subtype.mp hq
    · intro q _ r _ he
      exact Subtype.ext he
    · intro q hq
      refine ⟨⟨q,(Finset.mem_Icc.mp hq).1⟩,?_,rfl⟩
      exact Finset.mem_subtype.mpr hq
    · intro q _
      rfl
  change (∑ q∈(Finset.Icc 1 (N-1)).subtype (fun q : ℕ => 0<q),f q.val)=_
  rw [hs]
  have he : Finset.Icc 1 (N-1)=(Finset.range N).erase 0 := by
    ext q
    simp only [Finset.mem_Icc,Finset.mem_erase,Finset.mem_range]
    omega
  rw [he]
  by_cases hN : N=0
  · subst N
    simp
  · have hz : 0∈Finset.range N := Finset.mem_range.mpr (by omega)
    have hh := Finset.sum_erase_add (f := f) (s := Finset.range N) hz
    simpa only [hf0,add_zero] using hh

theorem uniform_singular_series_truncation {k u v L : ℕ} {b : ℕ → ℝ}
    (hb : Summable b)
    (hbound : ∀ n : ℤ,∀ q : ℕ,‖productSingularCoefficient k u v L n q‖≤b q)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ n : ℤ,
      ‖productSingularSeries k u v L n-
        ∑ q∈broadDenominators ((N-1 : ℕ) : ℝ),productSingularCoefficient k u v L n q‖<ε := by
  have ht := (tendsto_order.mp (natSeriesTail_tendsto_zero hb)).2 ε hε
  filter_upwards [ht] with N htail n
  rw [broadDenominators_sum_eq_range _ (productSingularCoefficient_zero k u v L n)]
  exact (complex_series_tail_bound hb (hbound n) N).trans_lt htail

theorem degree8_series_uniform_truncation (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ n : ℤ,
      ‖productSingularSeries 8 8 30 (L+1) n-
        ∑ q∈broadDenominators ((N-1 : ℕ) : ℝ),productSingularCoefficient 8 8 30 (L+1) n q‖<ε := by
  obtain ⟨C,_,hC⟩ := degree8_productSingularCoefficient_bound L
  exact uniform_singular_series_truncation
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left C) hC hε

theorem degree9_series_uniform_truncation (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ n : ℤ,
      ‖productSingularSeries 9 11 35 (L+1) n-
        ∑ q∈broadDenominators ((N-1 : ℕ) : ℝ),productSingularCoefficient 9 11 35 (L+1) n q‖<ε := by
  obtain ⟨C,_,hC⟩ := degree9_productSingularCoefficient_bound L
  exact uniform_singular_series_truncation
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left C) hC hε

#print axioms degree8_series_uniform_truncation
#print axioms degree9_series_uniform_truncation
end Waring.ProductBox
