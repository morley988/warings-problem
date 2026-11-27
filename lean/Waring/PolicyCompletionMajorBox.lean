import Waring.PolicyCompletionMajorBoxRanges

/-!
# The actual auxiliary major-arc estimate on the literal source boxes

The heights are floor(L/M_i^k), the coefficients are the original smooth
blocks M_i<m_i<=M_i R, and the centers are 1<=z<=L. Every arithmetic and
oscillatory estimate has been discharged; only the stated source ranges
and the explicit fixed lower threshold for R remain.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionMajorBox
open Polynomial PolicyCompletionMajorBoxRanges PolicyCompletionMajorHeight
open PolicyCompletionMajorFamily PolicyCompletionSourceMajorSize
open PolicyCompletionPhaseContent IntegerDifferencePolynomial
open CartesianProductSampling ProductMultiplicity RationalHeight AuxiliaryMajorArcs

/-- The fixed smoothness threshold is harmless when R=L^eta and eta>0. -/
def majorSmoothnessThreshold (k j : ℕ) : ℝ := 2*derivativeBoxConstant k j 1 (j:ℝ)

theorem source_box_major_pointwise (k j : ℕ) (hj : j+2≤k)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (L Q R : ℝ) (M : Fin j → ℝ),
      1≤L → 1≤R → (∀ i,1≤M i) → (∀ i,2≤boxHeights k L M i) →
      majorSmoothnessThreshold k j≤R^k → ∀ α : ℝ,
      MajorAtCutoff L ((boxConductor k L M/L)*R^(k*(k-j))) α →
      ‖boxSourceFamily k L Q R M α‖ ≤
        C₀*L^ε*L*(∏ i,boxHeights k L M i)*(∏ i,M i)*R^j*
          ((height (boxConductor k L M) α)^(-1/((k-j:ℕ):ℝ))+L^(-1/((k-j:ℕ):ℝ))) := by
  let B : ℝ := (j+1:ℕ)
  obtain ⟨C₀,hC₀,hfamily⟩ := source_family_intrinsic_majorant k j hj
    (B := B) (by dsimp [B]; positivity) hε (c := (2:ℝ)^j) (one_le_pow₀ (by norm_num))
  refine ⟨C₀,hC₀,?_⟩
  intro L Q R M hL hR hM hH hRlarge α hmajor
  have hLpos : 0<L := zero_lt_one.trans_le hL
  have hMpos : ∀ i,0<M i := fun i => zero_lt_one.trans_le (hM i)
  have hMprod : 0<∏ i,M i := Finset.prod_pos (fun i _ => hMpos i)
  have hHprod : 0<∏ i,boxHeights k L M i :=
    Finset.prod_pos (fun i _ => boxHeights_pos k hLpos hMpos i)
  let N := tupleProduct (boxHeightBounds k L M)
  have hN : 0<N := tupleProduct_pos _ (boxHeightBounds_pos k hH)
  have hNrange := boxHeightVolume_sandwich k hLpos hMpos hH
  have hNL : (N:ℝ)≤L^B := by
    have hb := (boxHeightVolume_power_bound k hL hM).trans
      (pow_le_pow_right₀ hL (Nat.le_succ j))
    simpa only [B,Real.rpow_natCast] using hb
  have hVL : boxConductor k L M=L^(k-j)*(∏ i,boxHeights k L M i) :=
    (boxHeightVolume_conductor (by omega) L M).symm
  have hVpos : 0<boxConductor k L M := by rw [hVL]; positivity
  have hVup : boxConductor k L M≤(2:ℝ)^j*L^(k-j)*(N:ℝ) := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^j)).mp hNrange.1
    rw [hVL]
    have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hLpos.le (k-j))
    nlinarith only [hm]
  obtain ⟨r,hr,herr⟩ := hmajor
  let q : ℕ := r.den
  let a : ℤ := r.num
  let β : ℝ := α-(r:ℝ)
  have hq : 0<q := r.pos
  letI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hα : (a:ℝ)/q+β=α := by
    dsimp [a,q,β]
    rw [Rat.cast_def]
    ring
  have ha : IsCoprime (q:ℤ) a := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [q,a,Int.natAbs_natCast] using r.reduced.symm
  have hqL : (q:ℝ)≤L := hr
  have hqB : (q:ℝ)≤L^B := by
    apply hqL.trans
    simpa only [B,Real.rpow_natCast] using le_self_pow₀ hL (by omega : j+1≠0)
  have hwidth : |β| *(∏ i,boxHeights k L M i)*L^(k-j-1)*R^(k*(k-j))≤1/(q:ℝ) := by
    let cutoff : ℝ := (boxConductor k L M/L)*R^(k*(k-j))
    have hXpos : 0 < cutoff := by dsimp [cutoff]; positivity
    have he : (q:ℝ)*|β|≤1/cutoff := by
      simpa only [RationalHeight.error,RationalHeight.denominator_error,q,β] using herr
    have hscale : cutoff=(∏ i,boxHeights k L M i)*L^(k-j-1)*R^(k*(k-j)) := by
      dsimp [cutoff]
      rw [hVL,show k-j=(k-j-1)+1 by omega,pow_succ]
      field_simp
      congr 1
    apply (le_div_iff₀ hqR).mpr
    have hh := (le_div_iff₀ hXpos).mp he
    rw [hscale] at hh
    nlinarith only [hh]
  have hsmall (h : Fin j → ℕ) (hh : h∈positiveBox (boxHeightBounds k L M))
      (m : Fin j → ℕ) (hm : m∈boxCoefficientTuples Q R M) :
      |β| *((powerPolynomial k (naturalParameters h m)).map (Int.castRingHom ℝ)).derivative.eval L
        ≤1/(2*(q:ℝ)) := by
    apply source_arc_derivative_small k j (CP := 1) (CS := (j:ℝ))
      (H := ∏ i,boxHeights k L M i) (by omega) hLpos hR hLpos.le hHprod.le
      (by norm_num) (Nat.cast_nonneg j) hqR (naturalParameters h m)
      (naturalParameters_length h m)
      (naturalParameters_pos h m (fun i => (mem_positiveBox.mp hh i).1)
        (boxCoefficientTuples_pos Q R M hm))
    · simp
    · rw [naturalParameters_heightProduct,Int.cast_natCast]
      have hprod := (Finset.mem_Icc.mp (positiveBox_product_range _ h hh)).2
      exact (by exact_mod_cast hprod : (tupleProduct h:ℝ)≤N).trans hNrange.2
    · exact box_shiftRadius_le k hLpos (zero_le_one.trans hR) hMpos hh hm
    · exact hwidth
    · exact hRlarge
  have hf := hfamily L hL q N hN hqL hqB hNL a
    (positiveBox (boxHeightBounds k L M)) (boxCoefficientTuples Q R M)
    (boxConductor k L M) β hVpos.le hVup ha
    (fun h hh i => (mem_positiveBox.mp hh i).1)
    (fun m hm => boxCoefficientTuples_pos Q R M hm)
    (fun h hh => positiveBox_product_range _ h hh) hsmall
  rw [hα] at hf
  change ‖boxSourceFamily k L Q R M α‖≤_ at hf
  have hcard := boxCoefficientTuples_card_le Q (zero_le_one.trans hR) (fun i => (hMpos i).le)
  apply hf.trans
  have hvol := mul_le_mul hcard hNrange.2 (Nat.cast_nonneg N)
    (mul_nonneg hMprod.le (pow_nonneg (zero_le_one.trans hR) j))
  let W : ℝ := (height (boxConductor k L M) α)^(-1/((k-j:ℕ):ℝ))+L^(-1/((k-j:ℕ):ℝ))
  have hW : 0≤W := add_nonneg
    (Real.rpow_nonneg (height_pos _ _).le _) (Real.rpow_nonneg hLpos.le _)
  have hb := mul_le_mul_of_nonneg_left hvol (by positivity : 0≤C₀*L^ε*L*W)
  convert hb using 1 <;> dsimp [W] <;> ring

#print axioms source_box_major_pointwise
end Waring.PolicyCompletionMajorBox
