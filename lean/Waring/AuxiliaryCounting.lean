import Waring.PowerDifferenceFibers

/-!
# The actual finite auxiliary zero-sum count

The blocks are triples of positive natural variables in the displayed ranges,
with value h^2*(m^k-n^k). The diagonal is counted exactly and the nonzero fibers
are controlled by the proved divisor injection. The resulting finite-prefix
count is the arithmetic part of the depth-six degree-eight auxiliary; relating
it to the efficient-difference polynomial integral remains a separate analytic
step.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryCounting
open PowerDifferenceFibers

private def blockOfPair (x : ℕ × (ℕ × ℕ)) : Block := ⟨x.1,x.2.1,x.2.2⟩

private theorem blockOfPair_injective : Function.Injective blockOfPair := by
  intro x y h
  exact Prod.ext (congrArg Block.h h)
    (Prod.ext (congrArg Block.m h) (congrArg Block.n h))

def blockRange (H M : ℕ) : Finset Block :=
  ((Finset.Icc 1 H) ×ˢ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))).image blockOfPair

theorem mem_blockRange {H M : ℕ} {x : Block} : x ∈ blockRange H M ↔
    x.h ∈ Finset.Icc 1 H ∧ x.m ∈ Finset.Icc 1 M ∧ x.n ∈ Finset.Icc 1 M := by
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(Finset.mem_product.mp hp).1,
      (Finset.mem_product.mp (Finset.mem_product.mp hp).2).1,
      (Finset.mem_product.mp (Finset.mem_product.mp hp).2).2⟩
  · rintro ⟨hh,hm,hn⟩
    exact Finset.mem_image.mpr ⟨(x.h,(x.m,x.n)),
      Finset.mem_product.mpr ⟨hh,Finset.mem_product.mpr ⟨hm,hn⟩⟩,by cases x; rfl⟩

theorem card_blockRange (H M : ℕ) : (blockRange H M).card = H*M^2 := by
  rw [blockRange,Finset.card_image_of_injective _ blockOfPair_injective]
  simp only [Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel]
  ring

theorem blockValue_eq_zero_iff {k : ℕ} (hk : 0 < k) {x : Block} (hh : 0 < x.h) :
    blockValue k x=0 ↔ x.m=x.n := by
  have hh0 : (x.h : ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hh.ne')
  rw [blockValue,mul_eq_zero,or_iff_right hh0,sub_eq_zero]
  constructor
  · intro hp
    apply (Nat.pow_left_strictMono hk.ne').injective
    exact_mod_cast hp
  · intro h
    rw [h]

theorem diagonal_card (k H M : ℕ) (hk : 0 < k) :
    ((blockRange H M).filter (fun x => blockValue k x=0)).card = H*M := by
  have heq : (blockRange H M).filter (fun x => blockValue k x=0) =
      ((Finset.Icc 1 H) ×ˢ (Finset.Icc 1 M)).image
        (fun p : ℕ × ℕ => (⟨p.1,p.2,p.2⟩ : Block)) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hr,hv⟩
      rcases mem_blockRange.mp hr with ⟨hh,hm,hn⟩
      have hmn := (blockValue_eq_zero_iff hk (by have := (Finset.mem_Icc.mp hh).1; omega)).mp hv
      refine Finset.mem_image.mpr ⟨(x.h,x.m),Finset.mem_product.mpr ⟨hh,hm⟩,?_⟩
      exact Block.ext rfl rfl hmn
    · intro hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      refine Finset.mem_filter.mpr ⟨mem_blockRange.mpr
        ⟨(Finset.mem_product.mp hp).1,(Finset.mem_product.mp hp).2,(Finset.mem_product.mp hp).2⟩,?_⟩
      simp [blockValue]
  rw [heq,Finset.card_image_of_injective]
  · simp only [Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel]
  · intro p q h
    exact Prod.ext (congrArg Block.h h) (congrArg Block.m h)

/-- All values in a coefficient block have an explicit polynomial size bound. -/
theorem blockValue_natAbs_le (k H M : ℕ) {x : Block} (hx : x ∈ blockRange H M) :
    (blockValue k x).natAbs ≤ H^2*M^k := by
  rcases mem_blockRange.mp hx with ⟨hh,hm,hn⟩
  have hm' : (x.m : ℤ)^k ≤ (M : ℤ)^k := by
    exact_mod_cast Nat.pow_le_pow_left (Finset.mem_Icc.mp hm).2 k
  have hn' : (x.n : ℤ)^k ≤ (M : ℤ)^k := by
    exact_mod_cast Nat.pow_le_pow_left (Finset.mem_Icc.mp hn).2 k
  have habs : |(x.m : ℤ)^k-(x.n : ℤ)^k| ≤ (M : ℤ)^k :=
    abs_le.mpr ⟨by have := pow_nonneg (Int.natCast_nonneg x.m) k; linarith,
      by have := pow_nonneg (Int.natCast_nonneg x.n) k; linarith⟩
  have hnat : ((x.m : ℤ)^k-(x.n : ℤ)^k).natAbs ≤ M^k := by
    have h' := habs
    rw [← Int.natCast_natAbs] at h'
    exact_mod_cast h'
  rw [blockValue,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (Finset.mem_Icc.mp hh).2 2) hnat

def sumValue (k : ℕ) (xs : List Block) : ℤ := (xs.map (blockValue k)).sum

def zeroCount (k : ℕ) (S : Finset (List Block)) : ℕ :=
  (S.filter (fun xs => sumValue k xs=0)).card

private def prependPair (p : List Block × Block) : List Block := p.2::p.1

private theorem prependPair_injective : Function.Injective prependPair := by
  intro p q h
  have hh := List.cons.inj h
  exact Prod.ext hh.2 hh.1

def extendFamily (S : Finset (List Block)) (B : Finset Block) : Finset (List Block) :=
  (S ×ˢ B).image prependPair

theorem card_extendFamily (S : Finset (List Block)) (B : Finset Block) :
    (extendFamily S B).card = S.card*B.card := by
  rw [extendFamily,Finset.card_image_of_injective _ prependPair_injective,Finset.card_product]

/-- Exact grouping of the new zero-sum solutions by their previous tuple. -/
theorem zeroCount_extendFamily (k : ℕ) (S : Finset (List Block)) (B : Finset Block) :
    zeroCount k (extendFamily S B) =
      ∑ xs ∈ S, (B.filter (fun x => blockValue k x = -sumValue k xs)).card := by
  unfold zeroCount extendFamily
  rw [Finset.filter_image,Finset.card_image_of_injective _ prependPair_injective]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro xs hxs
  apply Finset.sum_congr rfl
  intro x hx
  have heq : sumValue k (prependPair (xs,x))=0 ↔ blockValue k x = -sumValue k xs := by
    simp only [sumValue,prependPair,List.map_cons,List.sum_cons]
    omega
  simp only [heq]

/-- The genuine one-block count recurrence. The diagonal coefficient is exact;
only the off-diagonal part carries the nonzero-fiber bound E. -/
theorem zeroCount_step (k H M : ℕ) (hk : 0 < k) (S : Finset (List Block))
    {E : ℝ} (hE : 0 ≤ E)
    (hfiber : ∀ b : ℤ, b ≠ 0 →
      (((blockRange H M).filter (fun x => blockValue k x=b)).card : ℝ) ≤ E) :
    (zeroCount k (extendFamily S (blockRange H M)) : ℝ) ≤
      (H*M : ℕ)*(zeroCount k S : ℝ)+E*(S.card : ℝ) := by
  rw [zeroCount_extendFamily,Nat.cast_sum]
  have hpoint (xs : List Block) (hxs : xs ∈ S) :
      (((blockRange H M).filter (fun x => blockValue k x = -sumValue k xs)).card : ℝ) ≤
        (if sumValue k xs=0 then ((H*M : ℕ) : ℝ) else (0 : ℝ))+E := by
    by_cases hz : sumValue k xs=0
    · simp only [hz,neg_zero,if_pos,diagonal_card k H M hk]
      linarith
    · rw [if_neg hz,zero_add]
      exact hfiber _ (neg_ne_zero.mpr hz)
  calc
    _ ≤ ∑ xs ∈ S, ((if sumValue k xs=0 then ((H*M : ℕ) : ℝ) else (0 : ℝ))+E) :=
      Finset.sum_le_sum hpoint
    _ = (H*M : ℕ)*(zeroCount k S : ℝ)+E*(S.card : ℝ) := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,zeroCount]
      ring

/-- The divisor theorem supplies one uniform bound for every nonzero fiber
in every positive coefficient block of polynomial size. -/
theorem blockRange_nonzero_fibers_le_polynomial {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ k : ℕ, 2 ≤ k →
      ∀ H M : ℕ, ((H^2*M^k : ℕ) : ℝ) ≤ P^B →
      ∀ b : ℤ, b ≠ 0 →
        (((blockRange H M).filter (fun x => blockValue k x=b)).card : ℝ) ≤ C*P^ε := by
  obtain ⟨C,hC,hbound⟩ := block_fiber_card_le_polynomial hB hε
  refine ⟨C,hC,?_⟩
  intro P hP k hk H M hsize b hb
  let S := (blockRange H M).filter (fun x => blockValue k x=b)
  by_cases hS : S.Nonempty
  · obtain ⟨x,hx⟩ := hS
    have hv := (Finset.mem_filter.mp hx).2
    have hsz := blockValue_natAbs_le k H M (Finset.mem_filter.mp hx).1
    rw [hv] at hsz
    apply hbound P hP k hk S b hb
    · exact le_trans (by exact_mod_cast hsz) hsize
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
  · have he := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

/-- Actual ordered block tuples, with the most recently adjoined block first. -/
def prefixFamily (H M : ℕ → ℕ) : ℕ → Finset (List Block)
  | 0 => {[]}
  | i+1 => extendFamily (prefixFamily H M i) (blockRange (H i) (M i))

def diagonalProduct (H M : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∏ j ∈ Finset.range i, H j*M j

def volumeProduct (H M : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∏ j ∈ Finset.range i, H j*(M j)^2

theorem card_prefixFamily (H M : ℕ → ℕ) (i : ℕ) :
    (prefixFamily H M i).card = volumeProduct H M i := by
  induction i with
  | zero => simp [prefixFamily,volumeProduct]
  | succ i ih =>
    rw [prefixFamily,card_extendFamily,ih,card_blockRange]
    simp [volumeProduct,Finset.prod_range_succ]

theorem volumeProduct_eq (H M : ℕ → ℕ) (i : ℕ) :
    volumeProduct H M i = diagonalProduct H M i * ∏ j ∈ Finset.range i, M j := by
  simp only [volumeProduct,diagonalProduct,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  ring

/-- Exact finite induction under the displayed prefix-product inequalities.
Only the nonzero-fiber bound E is an input; it is discharged by the following
polynomial-size theorem. The dependence on the fixed depth is explicit. -/
theorem prefix_zeroCount_le (k : ℕ) (hk : 0 < k) (H M : ℕ → ℕ)
    (r : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hparam : ∀ i < r, (∏ j ∈ Finset.range i, M j) ≤ H i*M i)
    (hfiber : ∀ i < r, ∀ b : ℤ, b ≠ 0 →
      (((blockRange (H i) (M i)).filter (fun x => blockValue k x=b)).card : ℝ) ≤ E) :
    (zeroCount k (prefixFamily H M r) : ℝ) ≤
      (1+(r : ℝ)*E)*(diagonalProduct H M r : ℝ) := by
  induction r with
  | zero =>
    have hz : zeroCount k (prefixFamily H M 0) ≤ 1 := by
      simpa only [prefixFamily,Finset.card_singleton] using
        (Finset.card_filter_le (prefixFamily H M 0) (fun xs => sumValue k xs=0))
    simpa [diagonalProduct] using (show (zeroCount k (prefixFamily H M 0) : ℝ) ≤ 1 by exact_mod_cast hz)
  | succ r ih =>
    have hprev := ih (by intro i hi; exact hparam i (by omega))
      (by intro i hi; exact hfiber i (by omega))
    have hstep := zeroCount_step k (H r) (M r) hk (prefixFamily H M r) hE
      (hfiber r (by omega))
    rw [card_prefixFamily] at hstep
    have hvolume : (volumeProduct H M r : ℝ) ≤
        ((H r*M r : ℕ) : ℝ)*(diagonalProduct H M r : ℝ) := by
      rw [volumeProduct_eq,Nat.cast_mul]
      exact le_trans
        (mul_le_mul_of_nonneg_left (show (((∏ j ∈ Finset.range r, M j) : ℕ) : ℝ) ≤
          ((H r*M r : ℕ) : ℝ) by exact_mod_cast hparam r (by omega)) (by positivity))
        (by rw [mul_comm])
    have hdiag : diagonalProduct H M (r+1) = diagonalProduct H M r * (H r*M r) := by
      simp [diagonalProduct,Finset.prod_range_succ]
    change (zeroCount k (extendFamily (prefixFamily H M r) (blockRange (H r) (M r))) : ℝ) ≤ _
    calc
      _ ≤ ((H r*M r : ℕ) : ℝ)*(zeroCount k (prefixFamily H M r) : ℝ)+
          E*(volumeProduct H M r : ℝ) := hstep
      _ ≤ ((H r*M r : ℕ) : ℝ)*((1+(r : ℝ)*E)*(diagonalProduct H M r : ℝ))+
          E*(((H r*M r : ℕ) : ℝ)*(diagonalProduct H M r : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hprev (by positivity))
          (mul_le_mul_of_nonneg_left hvolume hE)
      _ = (1+((r+1 : ℕ) : ℝ)*E)*(diagonalProduct H M (r+1) : ℝ) := by
        rw [hdiag]
        simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
        ring

/-- Actual auxiliary zero-sum count with the conventional P^epsilon loss.
The coefficient boxes and every prefix-size condition are explicit. The bound
is uniform in the exponent k>=2; r and B are fixed before its constant is chosen. -/
theorem auxiliary_zeroCount_le_polynomial (r : ℕ) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ k : ℕ, 2 ≤ k →
      ∀ H M : ℕ → ℕ,
      (∀ i < r, ((H i^2*(M i)^k : ℕ) : ℝ) ≤ P^B) →
      (∀ i < r, (∏ j ∈ Finset.range i, M j) ≤ H i*M i) →
      (zeroCount k (prefixFamily H M r) : ℝ) ≤
        C*P^ε*(diagonalProduct H M r : ℝ) := by
  obtain ⟨D,hD,hfiber⟩ := blockRange_nonzero_fibers_le_polynomial hB hε
  refine ⟨1+(r : ℝ)*D,by positivity,?_⟩
  intro P hP k hk H M hsize hparam
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hPε : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hcount := prefix_zeroCount_le k (by omega) H M r
    (show 0 ≤ D*P^ε by positivity) hparam
    (by intro i hi; exact hfiber P hP k hk (H i) (M i) (hsize i hi))
  apply hcount.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith

/-- The actual arithmetic count used by the degree-eight depth-six auxiliary. -/
theorem degree8_depth6_zeroCount {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H M : ℕ → ℕ,
      (∀ i < 6, ((H i^2*(M i)^16 : ℕ) : ℝ) ≤ P^B) →
      (∀ i < 6, (∏ j ∈ Finset.range i, M j) ≤ H i*M i) →
      (zeroCount 16 (prefixFamily H M 6) : ℝ) ≤
        C*P^ε*(diagonalProduct H M 6 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := auxiliary_zeroCount_le_polynomial 6 hB hε
  exact ⟨C,hC,fun P hP H M => hbound P hP 16 (by norm_num) H M⟩

#print axioms zeroCount_step
#print axioms prefix_zeroCount_le
#print axioms auxiliary_zeroCount_le_polynomial
#print axioms degree8_depth6_zeroCount
end Waring.AuxiliaryCounting
