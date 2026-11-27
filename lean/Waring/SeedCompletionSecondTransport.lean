import Waring.SeedCompletionInitialMixed
import Waring.SeedCompletionEvenDoubleSource
import Waring.SeedCompletionNinthSecondFourthSource

/-!
# The literal second-stage aggregate inside the proved source terminal box

The encoding retains doubled old height, new positive height, both smooth
coefficients and the summed center. Every even-moment enlargement is an
injective finite solution-set comparison.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSecondTransport
open SmoothMoments FirstStageTransport SeedCompletionInitialMixed
open PolicyCompletionHolder IntegerDifferencePolynomial
open SeedCompletionBackward SeedCompletionBackwardCount SeedCompletionBackwardMoments
open SeedCompletionBackwardAggregate SeedCompletionNinthDoubleSource

abbrev SecondIndex := (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)
abbrev SecondLabel := Σ _ : (ℕ × ℕ) × ℕ, ℤ × ℤ

def secondDomain (P H₁ H₂ Q R M₁ M₂ : ℝ) : Finset SecondIndex :=
  sourceHeights H₁ H₂ ×ˢ (sourceCoefficients Q R M₁ M₂ ×ˢ sourceCenters P)

def secondPhase (k : ℕ) (x : SecondIndex) : ℤ :=
  (powerPolynomial k [((x.1.2 : ℤ),(x.2.1.2 : ℤ)),
    ((x.1.1 : ℤ),(x.2.1.1 : ℤ))]).eval (x.2.2 : ℤ)

def secondSum (k : ℕ) (P H₁ H₂ Q R M₁ M₂ α : ℝ) : ℂ :=
  frequencySum (secondDomain P H₁ H₂ Q R M₁ M₂) (secondPhase k) α

def firstNextDomain (k : ℕ) (P H Qc Q R M₁ M₂ : ℝ) : Finset SecondLabel :=
  aggregateNextDomain (firstLabels H Qc R M₁ ×ˢ CoefficientPower.coefficientBlock Q R M₂)
    (fun c => (c.2 : ℤ)) (⌊2*P⌋₊ : ℤ) k

def secondIndex (p : SecondLabel) : SecondIndex :=
  ((2*p.1.1.1,p.2.2.toNat),((p.1.1.2,p.1.2),p.2.1.toNat))

theorem firstNextDomain_bounds {k : ℕ} {P H Qc Q R M₁ M₂ : ℝ} {p : SecondLabel}
    (hp : p ∈ firstNextDomain k P H Qc Q R M₁ M₂) :
    p.1.1 ∈ firstLabels H Qc R M₁ ∧
      p.1.2 ∈ CoefficientPower.coefficientBlock Q R M₂ ∧
      2 ≤ p.2.1 ∧ p.2.1 ≤ 2*(⌊2*P⌋₊ : ℤ) ∧
      1 ≤ p.2.2 ∧ p.2.2 ≤ (⌊2*P⌋₊ : ℤ)/(p.1.2 : ℤ)^k := by
  rcases Finset.mem_sigma.mp hp with ⟨hc,hd⟩
  rcases Finset.mem_product.mp hd with ⟨hz,hh⟩
  exact ⟨(Finset.mem_product.mp hc).1,(Finset.mem_product.mp hc).2,
    (Finset.mem_Icc.mp hz).1,(Finset.mem_Icc.mp hz).2,
    (Finset.mem_Icc.mp hh).1,(Finset.mem_Icc.mp hh).2⟩

theorem secondIndex_injOn (k : ℕ) (P H Qc Q R M₁ M₂ : ℝ) :
    Set.InjOn secondIndex (↑(firstNextDomain k P H Qc Q R M₁ M₂) : Set SecondLabel) := by
  intro p hp q hq heq
  have hp := firstNextDomain_bounds hp
  have hq := firstNextDomain_bounds hq
  have hhold : 2*p.1.1.1=2*q.1.1.1 := congrArg (fun x : SecondIndex => x.1.1) heq
  have hhnew : p.2.2.toNat=q.2.2.toNat := congrArg (fun x : SecondIndex => x.1.2) heq
  have hm : p.1.1.2=q.1.1.2 := congrArg (fun x : SecondIndex => x.2.1.1) heq
  have hw : p.1.2=q.1.2 := congrArg (fun x : SecondIndex => x.2.1.2) heq
  have hz : p.2.1.toNat=q.2.1.toNat := congrArg (fun x : SecondIndex => x.2.2) heq
  have hh : p.1.1.1=q.1.1.1 := by omega
  have hhnew' : p.2.2=q.2.2 := by omega
  have hz' : p.2.1=q.2.1 := by omega
  rcases p with ⟨⟨⟨h,m⟩,w⟩,⟨z,t⟩⟩
  rcases q with ⟨⟨⟨h',m'⟩,w'⟩,⟨z',t'⟩⟩
  simp_all

theorem secondIndex_phase {k : ℕ} {P H Qc Q R M₁ M₂ : ℝ} {p : SecondLabel}
    (hp : p ∈ firstNextDomain k P H Qc Q R M₁ M₂) :
    secondPhase k (secondIndex p) =
      aggregateNextPhase k (fun c : (ℕ × ℕ) × ℕ => firstParameters c.1)
        (fun c => (c.2 : ℤ)) p := by
  have hp := firstNextDomain_bounds hp
  simp only [secondPhase,secondIndex,aggregateNextPhase,nextIntegerPhase,
    firstParameters,doubleHeights,List.map_cons,List.map_nil]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ p.2.2),
    Int.toNat_of_nonneg (by omega : 0 ≤ p.2.1)]
  push_cast
  rfl

theorem coefficientBlock_mono_length {Q S R M : ℝ} (hQS : Q ≤ S) :
    CoefficientPower.coefficientBlock Q R M ⊆ CoefficientPower.coefficientBlock S R M := by
  intro m hm
  obtain ⟨hm,hbounds⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨smoothNumbers_mono_length hQS hm,hbounds⟩

theorem secondIndex_image_subset (k : ℕ) {P H Qc Q R M₁ M₂ S H₁ H₂ Qt : ℝ}
    (hP : 0 ≤ P) (hH : 0 ≤ H) (hM₂ : 0 < M₂)
    (hPS : P ≤ S) (hHH₁ : H ≤ H₁) (hH₂ : 2*P/M₂^k ≤ H₂)
    (hQc : Qc ≤ Qt) (hQ : Q ≤ Qt) :
    (firstNextDomain k P H Qc Q R M₁ M₂).image secondIndex ⊆
      secondDomain S H₁ H₂ Qt R M₁ M₂ := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hold,hw,hzlo,hzhi,htlo,hthi⟩ := firstNextDomain_bounds hp
  obtain ⟨hhold,hmold⟩ := Finset.mem_product.mp hold
  have hhpos : 1 ≤ p.1.1.1 := (Finset.mem_Icc.mp hhold).1
  have hhH : (p.1.1.1 : ℝ) ≤ H :=
    (by exact_mod_cast (Finset.mem_Icc.mp hhold).2 : (p.1.1.1 : ℝ) ≤ ⌊H⌋₊).trans
      (Nat.floor_le hH)
  have hMw : M₂ < (p.1.2 : ℝ) := (Finset.mem_filter.mp hw).2.1
  have hwposN : 0 < p.1.2 := by exact_mod_cast (hM₂.trans hMw)
  have hwpos : 0 < (p.1.2 : ℤ)^k := pow_pos (by exact_mod_cast hwposN) _
  have htprod : p.2.2*(p.1.2 : ℤ)^k ≤ (⌊2*P⌋₊ : ℤ) :=
    (Int.le_ediv_iff_mul_le hwpos).mp hthi
  have htprodR : (p.2.2 : ℝ)*(p.1.2 : ℝ)^k ≤ (⌊2*P⌋₊ : ℝ) := by exact_mod_cast htprod
  have ht0 : 0 ≤ (p.2.2 : ℝ) := by exact_mod_cast (show 0 ≤ p.2.2 by omega)
  have htbound : (p.2.2 : ℝ) ≤ 2*P/M₂^k := by
    apply (le_div_iff₀ (pow_pos hM₂ _)).mpr
    calc
      _ ≤ (p.2.2 : ℝ)*(p.1.2 : ℝ)^k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM₂.le hMw.le _) ht0
      _ ≤ (⌊2*P⌋₊ : ℝ) := htprodR
      _ ≤ _ := Nat.floor_le (by positivity)
  have hzbound : (p.2.1 : ℝ) ≤ 4*S := by
    have hh : (p.2.1 : ℝ) ≤ 2*(⌊2*P⌋₊ : ℝ) := by exact_mod_cast hzhi
    have hf : (⌊2*P⌋₊ : ℝ) ≤ 2*P := Nat.floor_le (by positivity)
    linarith
  have htcast : ((p.2.2.toNat : ℕ) : ℝ)=(p.2.2 : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega : 0 ≤ p.2.2)]
  have hzcast : ((p.2.1.toNat : ℕ) : ℝ)=(p.2.1 : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega : 0 ≤ p.2.1)]
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨coefficientBlock_mono_length hQc hmold,
      coefficientBlock_mono_length hQ hw⟩,?_⟩⟩
  · apply Finset.mem_Icc.mpr
    refine ⟨by dsimp [secondIndex]; omega,?_⟩
    apply Nat.le_floor
    change ((2*p.1.1.1 : ℕ) : ℝ) ≤ 2*H₁
    push_cast
    linarith
  · apply Finset.mem_Icc.mpr
    refine ⟨by dsimp [secondIndex]; omega,?_⟩
    exact Nat.le_floor (htcast ▸ htbound.trans hH₂)
  · apply Finset.mem_Icc.mpr
    refine ⟨by dsimp [secondIndex]; omega,?_⟩
    exact Nat.le_floor (hzcast ▸ hzbound)

/-- Every actual even moment of the second aggregate is at most the
corresponding source terminal moment, with no parameter factor. -/
theorem first_next_moment_le_second (k r : ℕ) {P H Qc Q R M₁ M₂ S H₁ H₂ Qt : ℝ}
    (hP : 0 ≤ P) (hH : 0 ≤ H) (hM₂ : 0 < M₂)
    (hPS : P ≤ S) (hHH₁ : H ≤ H₁) (hH₂ : 2*P/M₂^k ≤ H₂)
    (hQc : Qc ≤ Qt) (hQ : Q ≤ Qt) :
    frequencyEvenMoment (firstNextDomain k P H Qc Q R M₁ M₂)
      (aggregateNextPhase k (fun c : (ℕ × ℕ) × ℕ => firstParameters c.1)
        (fun c => (c.2 : ℤ))) r ≤
      frequencyEvenMoment (secondDomain S H₁ H₂ Qt R M₁ M₂) (secondPhase k) r := by
  exact frequencyEvenMoment_le_of_injOn _ _ secondIndex
    (secondIndex_injOn k P H Qc Q R M₁ M₂) _ _ (fun _ hp => secondIndex_phase hp)
    (secondIndex_image_subset k hP hH hM₂ hPS hHH₁ hH₂ hQc hQ) r

theorem secondSum_ninth (P H₁ H₂ Q R M₁ M₂ α : ℝ) :
    secondSum 9 P H₁ H₂ Q R M₁ M₂ α=sourceNinthSecondSum P H₁ H₂ Q R M₁ M₂ α := rfl

theorem secondSum_even (d : ℕ) (P H₁ H₂ Q R M₁ M₂ α : ℝ) :
    secondSum (2*d) P H₁ H₂ Q R M₁ M₂ α=
      SeedCompletionEvenDoubleSource.sourceEvenSecondSum d P H₁ H₂ Q R M₁ M₂ α := rfl

#print axioms first_next_moment_le_second
end Waring.SeedCompletionSecondTransport
