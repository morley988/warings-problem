import Waring.SeedCompletionNaturalMoments

/-! # The actual absorbed recurrence on full source boxes

All derivative, positivity, phase, range and domain obligations are
proved from the displayed literal box bounds. The next auxiliary term
is the full source family with doubled center and smooth length.
-/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open IntegerDifferencePolynomial PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open CartesianProductSampling PolicyCompletionHolder PolicyCompletionSourceMajor
open EndgameCompletion SmoothMoments PolicyCompletionFundamental PolicyCompletionGoodBranch
open SeedCompletionSourceCount SeedCompletionAbsorbedFundamental CoefficientPower

theorem box_recurrence (k j s : ℕ) (hjk : j<k)
    {η ε : ℝ} (hη : 0<η) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∃ L₀ : ℝ,1≤L₀ ∧ ∀ L : ℝ,L₀≤L →
      ∀ (P R : ℝ) (M : Fin j → ℝ),
      (∀ i,1≤M i) → (∀ i,M i*R≤L) →
      ∀ Q V : ℝ,1≤V → V≤Q → Q≤L → V*R≤P → 2≤R → L^η≤R →
      boxMixedMoment k (s+1) L P R M Q≤
        K*L^ε*((naturalBoxLabels k L P R M).card:ℝ)*(V*R)^(2*(s+1)-1)*
          (((naturalBoxLabels k L P R M).card:ℝ)*(V*R)*((naturalCenters L).card:ℝ)*
              smoothMoment k (2*(s+1)) (Q/V) R+
            boxCrossMoment k (s+1) (2*L) P R (Fin.cons V M) (2*(Q/V))) := by
  obtain ⟨K,hK,L₀,hL₀,hrec⟩ := source_recurrence_count (κ := NaturalLabel j) k s hη hε
  refine ⟨2*K,by positivity,L₀,hL₀,?_⟩
  intro L hLL P R M hM hMR Q V hV hVQ hQL hVR hR hRL
  have hL : 1≤L := hL₀.trans hLL
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hQ : 1≤Q := hV.trans hVQ
  have hVp : 0<V := zero_lt_one.trans_le hV
  have hR0 : 0≤R := by linarith
  let C := naturalBoxLabels k L P R M
  let params := fun c : NaturalLabel j => naturalParameters c.1 c.2
  let Z := naturalCenters L
  have hparams : ∀ c∈C,∀ hm∈params c,0<hm.1 ∧ 0<hm.2 := by
    intro c hc
    obtain ⟨hh,hm⟩ := Finset.mem_product.mp hc
    exact naturalParameters_pos c.1 c.2
      (fun i => (mem_positiveBox.mp hh i).1) (boxCoefficientTuples_pos P R M hm)
  have hlength : ∀ c∈C,(params c).length<k := by
    intro c hc
    simpa only [params,naturalParameters_length] using hjk
  have hbox : ∀ c∈C,∀ hm∈params c,(hm.1:ℝ)≤L ∧ (hm.2:ℝ)≤L := by
    intro c hc
    obtain ⟨hh,hm⟩ := Finset.mem_product.mp hc
    simp only [params,naturalParameters,List.forall_mem_ofFn_iff,Int.cast_natCast]
    intro i
    have hHi : (c.1 i:ℝ)≤L/(M i)^k :=
      (by exact_mod_cast (mem_positiveBox.mp hh i).2 :
        (c.1 i:ℝ)≤(boxHeightBounds k L M i:ℝ)).trans
        (Nat.floor_le (div_nonneg hLp.le (pow_nonneg (zero_le_one.trans (hM i)) k)))
    exact ⟨hHi.trans (div_le_self hLp.le (one_le_pow₀ (hM i))),
      (boxCoefficientTuples_le P R M hm i).trans (hMR i)⟩
  have hN : ((⌊L⌋₊:ℤ):ℝ)≤L := by
    simpa only [Int.cast_natCast] using Nat.floor_le hLp.le
  have hf := hrec L hLL C params hparams hlength hbox (⌊L⌋₊:ℤ) hN Z
    (Finset.Subset.refl _) Q R V hV hVQ hQL hRL
  rw [sourceMixedMoment_eq_boxMixed] at hf
  have hT := commonModulus_sum_le_box k (s+1) Z hLp.le (zero_le_one.trans hQ) hVp
    (fun i => zero_lt_one.trans_le (hM i)) hVR hR (Finset.Subset.refl _)
  have hW := FirstStageTransport.coefficientBlock_card_le (P := Q)
    (mul_nonneg hVp.le hR0)
  have hU : 0≤smoothMoment k (2*(s+1)) (Q/V) R := smoothMoment_nonneg ..
  have hX := boxCrossMoment_nonneg k (s+1) (2*L) P R (Fin.cons V M) (2*(Q/V))
  have hT' : commonTotal k (s+1) C Z (fun c => powerPolynomial k (params c)) Q R V≤
      (C.card:ℝ)*(V*R)*(Z.card:ℝ)*smoothMoment k (2*(s+1)) (Q/V) R+
        2*boxCrossMoment k (s+1) (2*L) P R (Fin.cons V M) (2*(Q/V)) := by
    apply hT.trans
    gcongr
  apply hf.trans
  calc
    _ ≤ K*L^ε*((C.card:ℝ)^2*(Z.card:ℝ)*(V*R)^(2*(s+1))*
        smoothMoment k (2*(s+1)) (Q/V) R+
      (C.card:ℝ)*(V*R)^(2*(s+1)-1)*
        ((C.card:ℝ)*(V*R)*(Z.card:ℝ)*smoothMoment k (2*(s+1)) (Q/V) R+
          2*boxCrossMoment k (s+1) (2*L) P R (Fin.cons V M) (2*(Q/V)))) := by
      gcongr
    _ = _ := by
      have he : 2*(s+1)=(2*(s+1)-1)+1 := by omega
      have hp : (V*R)^(2*(s+1))=(V*R)^(2*(s+1)-1)*(V*R) :=
        (congrArg (fun n : ℕ => (V*R)^n) he).trans (pow_succ _ _)
      rw [hp]
      dsimp only [C,Z]
      ring

#print axioms box_recurrence
end Waring.SeedCompletionNaturalBox
