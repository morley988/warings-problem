import Waring.FirstDifferenceSource
import Waring.SeedCompletionTerminalHolder

/-!
# The literal first stage of efficient differencing

The initial mixed moment is exactly a pure smooth moment. The enlarged
integer center/height domain embeds into the natural-number source box.
Even moment comparison is made after integration, through the proved
nonnegative solution counts.
-/

noncomputable section
open scoped BigOperators

namespace Waring.FirstStageTransport
open SmoothMoments IntegerDifferencePolynomial FirstDifferenceSecond
open PolicyCompletionFundamental PolicyCompletionGoodBranch
open SeedCompletionBackwardCount SeedCompletionBackwardMoments
open SeedCompletionBackwardAggregate

def initialCenters (P R : ℝ) : Finset ℤ :=
  (smoothNumbers P R).image (fun n : ℕ => (n : ℤ))

theorem initialCenters_subset (P R : ℝ) :
    initialCenters P R ⊆ Finset.Icc 1 (⌊P⌋₊ : ℤ) := by
  intro z hz
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
  have hn := (mem_smoothNumbers.mp hn).1
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hn.1,by exact_mod_cast hn.2⟩

theorem initial_sourceMixedMoment (k s : ℕ) (P R : ℝ) :
    sourceMixedMoment k s ({()} : Finset Unit) (fun _ => [])
      (initialCenters P R) P R = smoothMoment k (2*(s+1)) P R := by
  classical
  rw [smoothMoment_even_eq_frequency]
  unfold sourceMixedMoment mixedFrequencyEvenMoment frequencyEvenMoment
  apply intervalIntegral.integral_congr
  intro α _
  dsimp only
  have hsum : (∑ x ∈ ({()} : Finset Unit) ×ˢ initialCenters P R,
      fourier (polynomialValue (fun _ : Unit => powerPolynomial k []) x)
        (α : AddCircle (1 : ℝ))) =
      ∑ n ∈ smoothNumbers P R,
        fourier ((n^k : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    simp only [Finset.sum_product,Finset.sum_singleton,initialCenters]
    rw [Finset.sum_image (by intro a _ b _ h; exact Int.natCast_inj.mp h)]
    apply Finset.sum_congr rfl
    intro n _
    simp [polynomialValue,powerPolynomial]
  rw [hsum]
  simp only [mul_one,show 2*(s+1)=2+2*s by omega,pow_add]

def firstFrequency (k : ℕ) (x : Index) : ℤ :=
  (powerPolynomial k [((x.1 : ℤ),(x.2.1 : ℤ))]).eval (x.2.2 : ℤ)

abbrev InitialLabel := Σ _ : Unit × ℕ, ℤ × ℤ

def firstIndex (p : InitialLabel) : Index :=
  (p.2.2.toNat,p.1.2,p.2.1.toNat)

def initialNextDomain (k : ℕ) (P R M : ℝ) : Finset InitialLabel :=
  aggregateNextDomain (({()} : Finset Unit) ×ˢ CoefficientPower.coefficientBlock P R M)
    (fun p => (p.2 : ℤ)) (⌊P⌋₊ : ℤ) k

theorem initialNextDomain_bounds {k : ℕ} {P R M : ℝ} {p : InitialLabel}
    (hp : p ∈ initialNextDomain k P R M) :
    p.1.2 ∈ CoefficientPower.coefficientBlock P R M ∧
      2 ≤ p.2.1 ∧ p.2.1 ≤ 2*(⌊P⌋₊ : ℤ) ∧
      1 ≤ p.2.2 ∧ p.2.2 ≤ (⌊P⌋₊ : ℤ)/(p.1.2 : ℤ)^k := by
  rcases Finset.mem_sigma.mp hp with ⟨hc,hd⟩
  have hm := (Finset.mem_product.mp hc).2
  rcases Finset.mem_product.mp hd with ⟨hz,hh⟩
  exact ⟨hm,(Finset.mem_Icc.mp hz).1,(Finset.mem_Icc.mp hz).2,
    (Finset.mem_Icc.mp hh).1,(Finset.mem_Icc.mp hh).2⟩

theorem firstIndex_injOn (k : ℕ) (P R M : ℝ) :
    Set.InjOn firstIndex (↑(initialNextDomain k P R M) : Set InitialLabel) := by
  intro p hp q hq heq
  have hp := initialNextDomain_bounds hp
  have hq := initialNextDomain_bounds hq
  have hh : p.2.2.toNat=q.2.2.toNat := congrArg Prod.fst heq
  have hm : p.1.2=q.1.2 := congrArg (fun x : Index => x.2.1) heq
  have hz : p.2.1.toNat=q.2.1.toNat := congrArg (fun x : Index => x.2.2) heq
  have hh' : p.2.2=q.2.2 := by omega
  have hz' : p.2.1=q.2.1 := by omega
  rcases p with ⟨⟨u,m⟩,⟨z,h⟩⟩
  rcases q with ⟨⟨v,n⟩,⟨y,j⟩⟩
  cases u; cases v
  simp_all

theorem firstIndex_phase {k : ℕ} {P R M : ℝ} {p : InitialLabel}
    (hp : p ∈ initialNextDomain k P R M) :
    firstFrequency k (firstIndex p) =
      aggregateNextPhase k (fun _ : Unit × ℕ => []) (fun p => (p.2 : ℤ)) p := by
  have hp := initialNextDomain_bounds hp
  simp only [firstFrequency,firstIndex,aggregateNextPhase,nextIntegerPhase,doubleHeights,
    List.map_nil]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ p.2.2),
    Int.toNat_of_nonneg (by omega : 0 ≤ p.2.1)]

/-- Injective relabeling and domain enlargement preserve the intended
inequality for actual even moments. -/
theorem frequencyEvenMoment_le_of_injOn {ι κ : Type*} [DecidableEq κ]
    (A : Finset ι) (B : Finset κ) (f : ι → κ)
    (hf : Set.InjOn f (↑A : Set ι)) (g : κ → ℤ) (a : ι → ℤ)
    (hphase : ∀ x ∈ A, g (f x)=a x) (hAB : A.image f ⊆ B) (r : ℕ) :
    frequencyEvenMoment A a r ≤ frequencyEvenMoment B g r := by
  have heq : frequencyEvenMoment A a r = frequencyEvenMoment (A.image f) g r := by
    unfold frequencyEvenMoment
    apply intervalIntegral.integral_congr
    intro α _
    dsimp only
    rw [Finset.sum_image (fun i hi j hj hij => hf hi hj hij)]
    congr 2
    apply Finset.sum_congr rfl
    intro x hx
    rw [hphase x hx]
  rw [heq]
  exact frequencyEvenMoment_mono hAB g r

theorem initialNextDomain_image_subset (k : ℕ) {P R M : ℝ}
    (hP : 1 ≤ P) (hM : 1 ≤ M) :
    (initialNextDomain k P R M).image firstIndex ⊆
      sourceFirstDomain P (P/M^k) P R M := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hw,hzlo,hzhi,hhlo,hhhi⟩ := initialNextDomain_bounds hp
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hMw : M < (p.1.2 : ℝ) := (Finset.mem_filter.mp hw).2.1
  have hwposN : 0 < p.1.2 := by exact_mod_cast (hMpos.trans hMw)
  have hwpos : 0 < (p.1.2 : ℤ)^k := pow_pos (by exact_mod_cast hwposN) _
  have hhprod : p.2.2*(p.1.2 : ℤ)^k ≤ (⌊P⌋₊ : ℤ) :=
    (Int.le_ediv_iff_mul_le hwpos).mp hhhi
  have hhprodR : (p.2.2 : ℝ)*(p.1.2 : ℝ)^k ≤ (⌊P⌋₊ : ℝ) := by
    exact_mod_cast hhprod
  have hh0 : 0 ≤ (p.2.2 : ℝ) := by exact_mod_cast (show 0 ≤ p.2.2 by omega)
  have hhbound : (p.2.2 : ℝ) ≤ P/M^k := by
    apply (le_div_iff₀ (pow_pos hMpos _)).mpr
    calc
      _ ≤ (p.2.2 : ℝ)*(p.1.2 : ℝ)^k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMw.le _) hh0
      _ ≤ (⌊P⌋₊ : ℝ) := hhprodR
      _ ≤ P := Nat.floor_le (zero_le_one.trans hP)
  have hzbound : (p.2.1 : ℝ) ≤ 2*P := by
    have h : (p.2.1 : ℝ) ≤ 2*(⌊P⌋₊ : ℝ) := by exact_mod_cast hzhi
    exact h.trans (mul_le_mul_of_nonneg_left (Nat.floor_le (zero_le_one.trans hP))
      (by norm_num))
  have hhcast : ((p.2.2.toNat : ℕ) : ℝ) = (p.2.2 : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega : 0 ≤ p.2.2)]
  have hzcast : ((p.2.1.toNat : ℕ) : ℝ) = (p.2.1 : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega : 0 ≤ p.2.1)]
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by dsimp [firstIndex]; omega,?_⟩,?_⟩
  · change p.2.2.toNat ≤ ⌊P/M^k⌋₊
    exact Nat.le_floor (hhcast ▸ hhbound)
  · apply Finset.mem_product.mpr
    refine ⟨hw,Finset.mem_Icc.mpr ⟨by dsimp [firstIndex]; omega,?_⟩⟩
    change p.2.1.toNat ≤ ⌊2*P⌋₊
    exact Nat.le_floor (hzcast ▸ hzbound)

/-- The actual first next-stage auxiliary moment is bounded by the full
source first-difference moment, with its original height P/M^k. -/
theorem initial_auxiliary_le_source (k r : ℕ) {P R M : ℝ}
    (hP : 1 ≤ P) (hM : 1 ≤ M) :
    frequencyEvenMoment (initialNextDomain k P R M)
      (aggregateNextPhase k (fun _ : Unit × ℕ => []) (fun p => (p.2 : ℤ))) r ≤
    frequencyEvenMoment (sourceFirstDomain P (P/M^k) P R M) (firstFrequency k) r := by
  exact frequencyEvenMoment_le_of_injOn _ _ firstIndex (firstIndex_injOn k P R M)
    _ _ (fun _ hp => firstIndex_phase hp) (initialNextDomain_image_subset k hP hM) r

#print axioms initial_sourceMixedMoment
#print axioms initial_auxiliary_le_source
end Waring.FirstStageTransport
