import Waring.SeedCompletionNaturalBox

/-! # Injective enlargement into the literal doubled source box -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open IntegerDifferencePolynomial PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open CartesianProductSampling PolicyCompletionHolder PolicyCompletionSourceMajor
open EndgameCompletion SmoothMoments SeedCompletionBackwardAggregate
open SeedCompletionBackwardMoments PolicyCompletionNextDomain CoefficientPower

theorem nextNaturalEncode_mem_box {j : ℕ} (k : ℕ)
    {L P Q R V : ℝ} {M : Fin j → ℝ}
    (hL : 0≤L) (hV : 0<V) (hM : ∀ i,0<M i) (hVR : V*R≤P)
    {p : NaturalNextLabel j}
    (hp : p∈aggregateNextDomain (naturalBoxLabels k L P R M ×ˢ coefficientBlock Q R V)
      (fun c => (c.2:ℤ)) (⌊L⌋₊:ℤ) k) :
    nextNaturalEncode p∈naturalBoxDomain k (2*L) P R (Fin.cons V M) := by
  classical
  obtain ⟨hc,hp⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hold,hw⟩ := Finset.mem_product.mp hc
  obtain ⟨hh,hm⟩ := Finset.mem_product.mp hold
  obtain ⟨hx,ht⟩ := Finset.mem_product.mp hp
  obtain ⟨hxlo,hxhi⟩ := Finset.mem_Icc.mp hx
  obtain ⟨htlo,hthi⟩ := Finset.mem_Icc.mp ht
  have hVw : V<(p.1.2:ℝ) := (Finset.mem_filter.mp hw).2.1
  have hwp : 0<(p.1.2:ℤ)^k := pow_pos (by exact_mod_cast hV.trans hVw) k
  have htprod : p.2.2*(p.1.2:ℤ)^k≤(⌊L⌋₊:ℤ) := (Int.le_ediv_iff_mul_le hwp).mp hthi
  have htprodR : (p.2.2:ℝ)*(p.1.2:ℝ)^k≤(⌊L⌋₊:ℝ) := by exact_mod_cast htprod
  have ht0 : 0≤(p.2.2:ℝ) := by exact_mod_cast (show 0≤p.2.2 by omega)
  have htbound : (p.2.2:ℝ)≤2*L/V^k := by
    apply (le_div_iff₀ (pow_pos hV k)).mpr
    calc
      _ ≤ (p.2.2:ℝ)*(p.1.2:ℝ)^k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV.le hVw.le k) ht0
      _ ≤ (⌊L⌋₊:ℝ) := htprodR
      _ ≤ L := Nat.floor_le hL
      _ ≤ 2*L := by linarith
  have htcast : ((p.2.2.toNat:ℕ):ℝ)=(p.2.2:ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega : 0≤p.2.2)]
  have hxcast : ((p.2.1.toNat:ℕ):ℝ)=(p.2.1:ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega : 0≤p.2.1)]
  have hxbound : (p.2.1:ℝ)≤2*L := by
    have H : (p.2.1:ℝ)≤2*(⌊L⌋₊:ℝ) := by exact_mod_cast hxhi
    linarith [Nat.floor_le hL]
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
  · apply mem_positiveBox.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · refine ⟨by change 1≤p.2.2.toNat; omega,?_⟩
      apply Nat.le_floor
      change ((p.2.2.toNat:ℕ):ℝ)≤2*L/V^k
      simpa only [htcast] using htbound
    · have hhi := mem_positiveBox.mp hh i
      have H : (p.1.1.1 i:ℝ)≤L/(M i)^k :=
        (by exact_mod_cast hhi.2 : (p.1.1.1 i:ℝ)≤(boxHeightBounds k L M i:ℝ)).trans
          (Nat.floor_le (div_nonneg hL (pow_nonneg (hM i).le k)))
      refine ⟨by change 1≤2*p.1.1.1 i; omega,?_⟩
      apply Nat.le_floor
      change ((2*p.1.1.1 i:ℕ):ℝ)≤2*L/(M i)^k
      push_cast
      calc
        _ ≤ 2*(L/(M i)^k) := mul_le_mul_of_nonneg_left H (by norm_num)
        _ = _ := by ring
  · apply Fintype.mem_piFinset.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · apply Finset.mem_filter.mpr
      exact ⟨smoothNumbers_mono_length hVR (coefficientBlock_subset Q R V hw),
        (Finset.mem_filter.mp hw).2⟩
    · exact Fintype.mem_piFinset.mp hm i
  · apply Finset.mem_Icc.mpr
    refine ⟨by change 1≤p.2.1.toNat; omega,?_⟩
    exact Nat.le_floor (hxcast ▸ hxbound)

#print axioms nextNaturalEncode_mem_box
end Waring.SeedCompletionNaturalBox
