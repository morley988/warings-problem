import Waring.SeedCompletionBackwardMoments
import Waring.PolicyCompletionHolder

/-!
# The small-variable branch of the fundamental lemma

The small-variable solutions are covered by the two sides and the `s`
possible marked positions. Their actual Fourier coefficient is bounded by
an integral with one short smooth factor. A scaled Young inequality then
absorbs the original moment, with an explicit constant depending only on
`s` and the branch-comparison constant. All finite summation domains are
retained; no pointwise comparison between a subsum and a full sum is used.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Waring.SeedCompletionSmall
open SeedCompletionBackwardCount SeedCompletionBackwardMoments
open PolicyCompletionHolder AuxiliaryL2Grouping

/-- Cross orthogonality for two arbitrary integer-frequency families. -/
theorem cross_count_eq_integral {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) :
    (((crossFrequencyPairs A B f g).card : ℝ) : ℂ) =
      ∫ x in (0 : ℝ)..1, frequencySum A f x * conj (frequencySum B g x) := by
  classical
  have hconj (x : ℝ) : conj (frequencySum B g x) =
      ∑ b ∈ B, fourier (-g b) (x : AddCircle (1 : ℝ)) := by
    unfold frequencySum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro b hb
    exact fourier_neg.symm
  have hpoint (x : ℝ) : frequencySum A f x * conj (frequencySum B g x) =
      ∑ p ∈ A ×ˢ B, fourier (f p.1-g p.2) (x : AddCircle (1 : ℝ)) := by
    rw [hconj]
    unfold frequencySum
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum,← fourier_add]
    rw [Finset.sum_product]
    rfl
  simp_rw [hpoint]
  have h := interval_integral_finite_frequency_coefficient (A ×ˢ B)
    (fun p => f p.1-g p.2) 0
  simp only [neg_zero,fourier_zero,mul_one,sub_eq_zero] at h
  unfold crossFrequencyPairs
  rw [h,Complex.ofReal_natCast]
  congr

/-- The absolute cross coefficient is bounded by the literal product norm. -/
theorem cross_count_le_integral_norm {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) :
    ((crossFrequencyPairs A B f g).card : ℝ) ≤
      ∫ x in (0 : ℝ)..1, ‖frequencySum A f x‖ * ‖frequencySum B g x‖ := by
  have h := intervalIntegral.norm_integral_le_integral_norm (f := fun x : ℝ =>
    frequencySum A f x * conj (frequencySum B g x)) (μ := volume) zero_le_one
  rw [← cross_count_eq_integral] at h
  simpa only [Complex.norm_real,Real.norm_natCast,norm_mul,Complex.norm_conj] using h

/-- Exact product expansion with a separate finite set at every position. -/
theorem frequencySum_heterogeneous {α β : Type*} (s : ℕ) (A : Finset α)
    (B : Fin s → Finset β) (f : α → ℤ) (g : β → ℤ) (x : ℝ) :
    frequencySum (A ×ˢ Fintype.piFinset B) (tupleFrequency f (fun _ => g)) x =
      frequencySum A f x * ∏ i, frequencySum (B i) g x := by
  classical
  unfold frequencySum
  rw [Finset.prod_univ_sum]
  simp only [Finset.sum_mul,Finset.mul_sum]
  simp_rw [prod_fourier_character]
  simp only [← fourier_add]
  rw [Finset.sum_product]
  exact Finset.sum_comm

/-- A product with one distinguished factor. -/
theorem prod_marked {M : Type*} [CommMonoid M] {s : ℕ} (i : Fin s) (a b : M) :
    (∏ j : Fin s, if j=i then a else b) = a*b^(s-1) := by
  rw [Finset.prod_ite]
  simp [Finset.filter_eq',Finset.filter_ne',Finset.card_erase_of_mem]

def markedEndpoints {α β : Type*} (s : ℕ) (A : Finset α) (B D : Finset β)
    (i : Fin s) : Finset (α × (Fin s → β)) :=
  A ×ˢ Fintype.piFinset (fun j => if j=i then D else B)

theorem frequencySum_marked {α β : Type*} (s : ℕ) (A : Finset α) (B D : Finset β)
    (i : Fin s) (f : α → ℤ) (g : β → ℤ) (x : ℝ) :
    frequencySum (markedEndpoints s A B D i) (tupleFrequency f (fun _ => g)) x =
      frequencySum A f x * (frequencySum D g x * (frequencySum B g x)^(s-1)) := by
  unfold markedEndpoints
  rw [frequencySum_heterogeneous]
  have hpoint (j : Fin s) :
      frequencySum (if j=i then D else B) g x =
        if j=i then frequencySum D g x else frequencySum B g x := by split_ifs <;> rfl
  simp_rw [hpoint]
  rw [prod_marked]

theorem frequencySum_homogeneous {α β : Type*} (s : ℕ) (A : Finset α) (B : Finset β)
    (f : α → ℤ) (g : β → ℤ) (x : ℝ) :
    frequencySum (A ×ˢ finiteTuples B s) (tupleFrequency f (fun _ => g)) x =
      frequencySum A f x * (frequencySum B g x)^s := by
  rw [frequencySum_tuple]
  simp

/-- The marked-position cross count has exactly one short norm factor. -/
theorem marked_cross_le {α β : Type*} (s : ℕ) (hs : 0 < s) (A : Finset α) (B D : Finset β)
    (i : Fin s) (f : α → ℤ) (g : β → ℤ) :
    ((crossFrequencyPairs (markedEndpoints s A B D i) (A ×ˢ finiteTuples B s)
      (tupleFrequency f (fun _ => g)) (tupleFrequency f (fun _ => g))).card : ℝ) ≤
      ∫ x in (0 : ℝ)..1, ‖frequencySum A f x‖^2 * ‖frequencySum D g x‖ *
        ‖frequencySum B g x‖^(2*s-1) := by
  have h := cross_count_le_integral_norm (markedEndpoints s A B D i)
    (A ×ˢ finiteTuples B s) (tupleFrequency f (fun _ => g)) (tupleFrequency f (fun _ => g))
  have heq (x : ℝ) :
      ‖frequencySum (markedEndpoints s A B D i) (tupleFrequency f (fun _ => g)) x‖ *
      ‖frequencySum (A ×ˢ finiteTuples B s) (tupleFrequency f (fun _ => g)) x‖ =
      ‖frequencySum A f x‖^2 * ‖frequencySum D g x‖ * ‖frequencySum B g x‖^(2*s-1) := by
    rw [frequencySum_marked,frequencySum_homogeneous]
    simp only [norm_mul,norm_pow]
    have hn : s-1+s=2*s-1 := by omega
    rw [← hn,pow_add]
    ring
  simpa only [heq] using h

/-- A natural-power form of scaled Young, sufficient for absorption. -/
theorem scaled_young {n : ℕ} (hn : 0 < n) (t d b : ℝ)
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hb : 0 ≤ b) :
    t*d*b^(n-1) ≤ b^n+t^n*d^n := by
  have he : n-1+1=n := by omega
  have hp : (t*d)^n=t^n*d^n := mul_pow _ _ _
  by_cases h : t*d ≤ b
  · calc
      _ ≤ b*b^(n-1) := mul_le_mul_of_nonneg_right h (pow_nonneg hb _)
      _ = b^n := by rw [← pow_succ',he]
      _ ≤ b^n+t^n*d^n := le_add_of_nonneg_right (mul_nonneg (pow_nonneg ht _) (pow_nonneg hd _))
  · have hb' : b ≤ t*d := le_of_not_ge h
    calc
      _ ≤ t*d*(t*d)^(n-1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hb hb' _) (mul_nonneg ht hd)
      _ = t^n*d^n := by rw [← pow_succ',he,hp]
      _ ≤ b^n+t^n*d^n := le_add_of_nonneg_left (pow_nonneg hb _)

/-- Swapping the two frequency families does not change the cross count. -/
theorem cross_count_swap {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) :
    (crossFrequencyPairs A B f g).card = (crossFrequencyPairs B A g f).card := by
  classical
  apply Finset.card_equiv (Equiv.prodComm ι κ)
  intro p
  simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product,
    Equiv.prodComm_apply]
  tauto

/-- A literal collision having at least one short smooth variable on either side. -/
def smallTupleCollisions {α β : Type*} (s : ℕ) (A : Finset α) (B D : Finset β)
    (f : α → ℤ) (g : β → ℤ) := by
  classical
  exact (tupleCollision s A B f (fun _ => g)).filter
    (fun p => ∃ i, p.1.2 i ∈ D ∨ p.2.2 i ∈ D)

theorem mem_markedEndpoints_of_mem {α β : Type*} (s : ℕ) (A : Finset α)
    (B D : Finset β) (i : Fin s) (p : α × (Fin s → β))
    (hp : p ∈ A ×ˢ finiteTuples B s) (hi : p.2 i ∈ D) :
    p ∈ markedEndpoints s A B D i := by
  classical
  rcases Finset.mem_product.mp hp with ⟨ha,hu⟩
  apply Finset.mem_product.mpr
  refine ⟨ha,Fintype.mem_piFinset.mpr ?_⟩
  intro j
  by_cases hji : j=i
  · simpa only [hji,ite_true] using hi
  · simpa only [if_neg hji] using (Fintype.mem_piFinset.mp hu j)

/-- The two sides and `s` positions cover every actual small-variable solution. -/
theorem small_count_le_marked {α β : Type*} (s : ℕ) (A : Finset α) (B D : Finset β)
    (f : α → ℤ) (g : β → ℤ) :
    (smallTupleCollisions s A B D f g).card ≤
      2*∑ i : Fin s,
        (crossFrequencyPairs (markedEndpoints s A B D i) (A ×ˢ finiteTuples B s)
          (tupleFrequency f (fun _ => g)) (tupleFrequency f (fun _ => g))).card := by
  classical
  let X := A ×ˢ finiteTuples B s
  let T := tupleFrequency f (fun _ : Fin s => g)
  let L (i : Fin s) := crossFrequencyPairs (markedEndpoints s A B D i) X T T
  let R (i : Fin s) := crossFrequencyPairs X (markedEndpoints s A B D i) T T
  have hsub : smallTupleCollisions s A B D f g ⊆
      Finset.univ.biUnion (fun i : Fin s => L i ∪ R i) := by
    intro p hp
    obtain ⟨hp,i,hi⟩ := Finset.mem_filter.mp hp
    obtain ⟨hdom,heq⟩ := Finset.mem_filter.mp hp
    rcases Finset.mem_product.mp hdom with ⟨hleft,hright⟩
    refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩
    rcases hi with hi | hi
    · apply Finset.mem_union_left
      change p ∈ crossFrequencyPairs (markedEndpoints s A B D i) X T T
      simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product]
      exact ⟨⟨mem_markedEndpoints_of_mem s A B D i p.1 hleft hi,hright⟩,heq⟩
    · apply Finset.mem_union_right
      change p ∈ crossFrequencyPairs X (markedEndpoints s A B D i) T T
      simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product]
      exact ⟨⟨hleft,mem_markedEndpoints_of_mem s A B D i p.2 hright hi⟩,heq⟩
  have heq (i : Fin s) : (R i).card=(L i).card :=
    cross_count_swap X (markedEndpoints s A B D i) T T
  calc
    _ ≤ (Finset.univ.biUnion (fun i : Fin s => L i ∪ R i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin s, (L i ∪ R i).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin s, 2*(L i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.card_union_le _ _).trans_eq (by rw [heq]; omega)
    _ = _ := by rw [Finset.mul_sum]

/-- The genuine small-variable count is bounded by one marked integral. -/
theorem small_count_le_integral {α β : Type*} (s : ℕ) (hs : 0 < s)
    (A : Finset α) (B D : Finset β) (f : α → ℤ) (g : β → ℤ) :
    ((smallTupleCollisions s A B D f g).card : ℝ) ≤
      (2*(s : ℝ)) * (∫ x in (0 : ℝ)..1,
        ‖frequencySum A f x‖^2 * ‖frequencySum D g x‖ * ‖frequencySum B g x‖^(2*s-1)) := by
  have hc : ((smallTupleCollisions s A B D f g).card : ℝ) ≤
      2*∑ i : Fin s,
        ((crossFrequencyPairs (markedEndpoints s A B D i) (A ×ˢ finiteTuples B s)
          (tupleFrequency f (fun _ => g)) (tupleFrequency f (fun _ => g))).card : ℝ) := by
    exact_mod_cast small_count_le_marked s A B D f g
  apply hc.trans
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s)))
    (fun i hi => marked_cross_le s hs A B D i f g)
  have hm := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hm

/-- Pointwise scaled Young integrated with the unchanged auxiliary weight. -/
theorem marked_integral_young {α β : Type*} (s : ℕ) (hs : 0 < s)
    (A : Finset α) (B D : Finset β) (f : α → ℤ) (g : β → ℤ)
    (t : ℝ) (ht : 0 ≤ t) :
    t*(∫ x in (0 : ℝ)..1,
      ‖frequencySum A f x‖^2 * ‖frequencySum D g x‖ * ‖frequencySum B g x‖^(2*s-1)) ≤
      mixedFrequencyEvenMoment A f 1 B g s + t^(2*s)*mixedFrequencyEvenMoment A f 1 D g s := by
  have hF := (continuous_frequencySum A f).norm.pow 2
  have hB := (continuous_frequencySum B g).norm
  have hD := (continuous_frequencySum D g).norm
  have hleft : Continuous (fun x : ℝ => t*(‖frequencySum A f x‖^2 *
      ‖frequencySum D g x‖ * ‖frequencySum B g x‖^(2*s-1))) :=
    continuous_const.mul ((hF.mul hD).mul (hB.pow (2*s-1)))
  have hright : Continuous (fun x : ℝ =>
      ‖frequencySum A f x‖^2*‖frequencySum B g x‖^(2*s) +
      t^(2*s)*(‖frequencySum A f x‖^2*‖frequencySum D g x‖^(2*s))) :=
    (hF.mul (hB.pow (2*s))).add
      (continuous_const.mul (hF.mul (hD.pow (2*s))))
  have hpoint (x : ℝ) :
      t*(‖frequencySum A f x‖^2 * ‖frequencySum D g x‖ * ‖frequencySum B g x‖^(2*s-1)) ≤
      ‖frequencySum A f x‖^2*‖frequencySum B g x‖^(2*s) +
        t^(2*s)*(‖frequencySum A f x‖^2*‖frequencySum D g x‖^(2*s)) := by
    have h := mul_le_mul_of_nonneg_left
      (scaled_young (by omega : 0 < 2*s) t ‖frequencySum D g x‖ ‖frequencySum B g x‖
        ht (norm_nonneg _) (norm_nonneg _)) (sq_nonneg ‖frequencySum A f x‖)
    nlinarith only [h]
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hleft.intervalIntegrable 0 1) (hright.intervalIntegrable 0 1) (fun x hx => hpoint x)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((hF.mul (hB.pow (2*s))).intervalIntegrable 0 1)
    ((continuous_const.mul (hF.mul (hD.pow (2*s)))).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul] at h
  simpa only [mixedFrequencyEvenMoment,frequencySum,mul_one] using h

/-- If the small-variable branch dominates, the complete original moment
is bounded by the same moment with every smooth variable in the short set.
The explicit constant is harmless in the source's fixed-`s` estimate. -/
theorem small_branch_absorption {α β : Type*} (s : ℕ) (hs : 0 < s)
    (A : Finset α) (B D : Finset β) (f : α → ℤ) (g : β → ℤ)
    (K : ℝ) (hK : 0 ≤ K)
    (hdom : mixedFrequencyEvenMoment A f 1 B g s ≤
      K*((smallTupleCollisions s A B D f g).card : ℝ)) :
    mixedFrequencyEvenMoment A f 1 B g s ≤
      (4*K*(s : ℝ))^(2*s)*mixedFrequencyEvenMoment A f 1 D g s := by
  let I := ∫ x in (0 : ℝ)..1,
    ‖frequencySum A f x‖^2 * ‖frequencySum D g x‖ * ‖frequencySum B g x‖^(2*s-1)
  have hmark : mixedFrequencyEvenMoment A f 1 B g s ≤ K*(2*(s : ℝ))*I := by
    have h := hdom.trans (mul_le_mul_of_nonneg_left
      (small_count_le_integral s hs A B D f g) hK)
    change mixedFrequencyEvenMoment A f 1 B g s ≤ K*((2*(s : ℝ))*I) at h
    simpa only [mul_assoc] using h
  have hyoung := marked_integral_young s hs A B D f g (4*K*(s : ℝ)) (by positivity)
  change (4*K*(s : ℝ))*I ≤ _ at hyoung
  nlinarith only [hmark,hyoung]

/-- Absorption can retain the other branches as an explicit remainder. -/
theorem small_branch_absorption_with_remainder {α β : Type*} (s : ℕ) (hs : 0 < s)
    (A : Finset α) (B D : Finset β) (f : α → ℤ) (g : β → ℤ)
    (K E : ℝ) (hK : 0 ≤ K)
    (hdom : mixedFrequencyEvenMoment A f 1 B g s ≤
      K*(((smallTupleCollisions s A B D f g).card : ℝ)+E)) :
    mixedFrequencyEvenMoment A f 1 B g s ≤
      (4*K*(s : ℝ))^(2*s)*mixedFrequencyEvenMoment A f 1 D g s + 2*K*E := by
  let I := ∫ x in (0 : ℝ)..1,
    ‖frequencySum A f x‖^2 * ‖frequencySum D g x‖ * ‖frequencySum B g x‖^(2*s-1)
  have hmark : mixedFrequencyEvenMoment A f 1 B g s ≤ K*((2*(s : ℝ))*I+E) := by
    exact hdom.trans (mul_le_mul_of_nonneg_left
      (add_le_add_right (small_count_le_integral s hs A B D f g) E) hK)
  have hyoung := marked_integral_young s hs A B D f g (4*K*(s : ℝ)) (by positivity)
  change (4*K*(s : ℝ))*I ≤ _ at hyoung
  nlinarith only [hmark,hyoung]

/-- Within the actual long smooth set, the short-set condition is exactly
that the variable is at most the short length. -/
theorem mem_short_smooth_iff {Q R M : ℝ} (hM : 0 ≤ M) {n : ℕ}
    (hn : n ∈ SmoothMoments.smoothNumbers Q R) :
    n ∈ SmoothMoments.smoothNumbers M R ↔ (n : ℝ) ≤ M := by
  rcases SmoothMoments.mem_smoothNumbers.mp hn with ⟨⟨hnpos,hnQ⟩,hsmooth⟩
  rw [SmoothMoments.mem_smoothNumbers]
  constructor
  · intro h
    exact (Nat.le_floor_iff hM).mp h.1.2
  · intro h
    exact ⟨⟨hnpos,(Nat.le_floor_iff hM).mpr h⟩,hsmooth⟩

/-- Literal small-variable solutions on the original smooth domain. -/
def smallSmoothSolutions {α : Type*} (s k : ℕ) (A : Finset α) (f : α → ℤ)
    (Q R M : ℝ) := by
  classical
  exact (tupleCollision s A (SmoothMoments.smoothNumbers Q R) f
    (fun _ n => (n : ℤ)^k)).filter
      (fun p => ∃ i, (p.1.2 i : ℝ) ≤ M ∨ (p.2.2 i : ℝ) ≤ M)

theorem smallSmoothSolutions_eq {α : Type*} (s k : ℕ) (A : Finset α) (f : α → ℤ)
    (Q R M : ℝ) (hM : 0 ≤ M) :
    smallSmoothSolutions s k A f Q R M =
      smallTupleCollisions s A (SmoothMoments.smoothNumbers Q R)
        (SmoothMoments.smoothNumbers M R) f (fun n => (n : ℤ)^k) := by
  classical
  unfold smallSmoothSolutions smallTupleCollisions
  ext p
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hp
  rcases Finset.mem_filter.mp hp with ⟨hdom,heq⟩
  rcases Finset.mem_product.mp hdom with ⟨hleft,hright⟩
  have hl (i : Fin s) : p.1.2 i ∈ SmoothMoments.smoothNumbers Q R :=
    Fintype.mem_piFinset.mp (Finset.mem_product.mp hleft).2 i
  have hr (i : Fin s) : p.2.2 i ∈ SmoothMoments.smoothNumbers Q R :=
    Fintype.mem_piFinset.mp (Finset.mem_product.mp hright).2 i
  simp_rw [mem_short_smooth_iff hM (hl _),mem_short_smooth_iff hM (hr _)]

/-- The source's first branch with both literal smooth summation sets. -/
theorem small_smooth_branch_absorption {α : Type*} (s k : ℕ) (hs : 0 < s)
    (A : Finset α) (f : α → ℤ) (Q R M K : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hdom : mixedFrequencyEvenMoment A f 1 (SmoothMoments.smoothNumbers Q R)
      (fun n => (n : ℤ)^k) s ≤ K*((smallSmoothSolutions s k A f Q R M).card : ℝ)) :
    mixedFrequencyEvenMoment A f 1 (SmoothMoments.smoothNumbers Q R)
      (fun n => (n : ℤ)^k) s ≤
      (4*K*(s : ℝ))^(2*s)*mixedFrequencyEvenMoment A f 1
        (SmoothMoments.smoothNumbers M R) (fun n => (n : ℤ)^k) s := by
  rw [smallSmoothSolutions_eq s k A f Q R M hM] at hdom
  exact small_branch_absorption s hs A (SmoothMoments.smoothNumbers Q R)
    (SmoothMoments.smoothNumbers M R) f (fun n => (n : ℤ)^k) K hK hdom

#print axioms cross_count_le_integral_norm
#print axioms marked_cross_le
#print axioms scaled_young
#print axioms small_count_le_integral
#print axioms small_branch_absorption
#print axioms small_branch_absorption_with_remainder
#print axioms small_smooth_branch_absorption

end Waring.SeedCompletionSmall
