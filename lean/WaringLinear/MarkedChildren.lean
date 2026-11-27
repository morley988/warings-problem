import WaringLinear.MarkedMass
import WaringLinear.ScalarMarkedStates
import Waring.SmoothMoments

/-! Exact deletion of any specified group of marked prime factors, including
the divisors of the inclusion--exclusion branch. -/
noncomputable section
open Finset
open scoped Classical BigOperators
namespace WaringLinear.MarkedMass

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem split_product (a : ι ⊕ κ → ℕ) :
    (∏ i,a i) = (∏ i,a (.inl i)) * ∏ j,a (.inr j) := Fintype.prod_sum_type a

private theorem picked_dvd_iff (P : ℝ) (W : ι ⊕ κ → Finset ℕ)
    (H : ∀ i, ∀ p ∈ W i, Nat.Prime p)
    (hs : ∀ i j, ∀ p ∈ W i, p ∈ W j → i=j)
    (hsmall : ∀ a ∈ Fintype.piFinset W, ∀ i, ∀ p ∈ W i, P/((∏ j,a j:ℕ):ℝ)<p)
    (b : ι → ℕ) (hb : ∀ i, b i ∈ W (.inl i))
    (a : ι ⊕ κ → ℕ) (ha : ∀ i, a i ∈ W i)
    (y : ℕ) (hy : 1 ≤ y) (hmax : y ≤ ⌊P / ((∏ i,a i:ℕ):ℝ)⌋₊) :
    (∏ i,b i) ∣ y * ∏ i,a i ↔ ∀ i, a (.inl i) = b i := by
  constructor
  · intro hd i
    have hy' : (y : ℝ) ≤ P / ((∏ j,a j:ℕ):ℝ) := by
      have hp : 0 < ⌊P/((∏ j,a j:ℕ):ℝ)⌋₊ := by omega
      exact (le_trans (by exact_mod_cast hmax) (Nat.floor_le ((Nat.floor_pos.mp hp).trans' zero_le_one)))
    have hny : ¬ b i ∣ y := fun hd' => (not_le_of_gt (hy'.trans_lt
      (hsmall a (Fintype.mem_piFinset.mpr ha) (.inl i) _ (hb i))))
        (by exact_mod_cast Nat.le_of_dvd hy hd')
    apply (WaringLinear.marked_coordinate_divides_iff (.inl i) (b i) y a
      (H _ _ (hb i)) (fun j => H _ _ (ha j)) hny (fun j he =>
        hs j (.inl i) _ (ha j) (he ▸ hb i))).mp
    exact dvd_trans (dvd_prod_of_mem b (mem_univ i)) hd
  · intro he
    rw [split_product, ←mul_assoc, mul_comm y, mul_assoc,
      show (∏ i, a (.inl i)) = ∏ i,b i from prod_congr rfl (fun i _ => he i)]
    exact dvd_mul_right _ _

/-- Division by a product of fixed marks gives exactly the support with those
windows removed. This also applies to any subproduct on an exceptional branch. -/
theorem divided_marked_group (P : ℝ) (W : ι ⊕ κ → Finset ℕ)
    (H : ∀ i, ∀ p ∈ W i, Nat.Prime p)
    (hs : ∀ i j, ∀ p ∈ W i, p ∈ W j → i=j)
    (hsmall : ∀ a ∈ Fintype.piFinset W, ∀ i, ∀ p ∈ W i, P/((∏ j,a j:ℕ):ℝ)<p)
    (b : ι → ℕ) (hb : ∀ i,b i∈W (.inl i)) :
    WaringLinear.dividedState (roots P W) (∏ i,b i) =
    roots (P/((∏ i,b i:ℕ):ℝ)) (fun j => W (.inr j)) := by
  have hpos : 0 < ∏ i,b i := prod_pos (fun i _ => (H _ _ (hb i)).pos)
  have hprod (a : ι ⊕ κ → ℕ) (he : ∀ i, a (.inl i)=b i) :
      (∏ i,a i) = (∏ i,b i)*∏ j,a (.inr j) := by
    rw [split_product, prod_congr rfl (fun i _ => he i)]
  ext n
  constructor
  · intro hn
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hn
    obtain ⟨ht,hd⟩ := mem_filter.mp ht
    obtain ⟨a,y,ha,hy,hmax,rfl⟩ := mem_roots.mp ht
    have he := (picked_dvd_iff P W H hs hsmall b hb a ha y hy hmax).mp hd
    refine mem_roots.mpr ⟨fun j => a (.inr j),y,(fun j => ha (.inr j)),hy,?_,?_⟩
    · simpa only [hprod a he, Nat.cast_mul,div_div] using hmax
    · rw [hprod a he, ← mul_left_comm, Nat.mul_div_cancel_left _ hpos]
  · intro hn
    obtain ⟨a,y,ha,hy,hmax,rfl⟩ := mem_roots.mp hn
    let c : ι ⊕ κ → ℕ := Sum.elim b a
    have hc : ∀ i, c i ∈ W i := by rintro (i|j); exacts [hb i,ha j]
    have hprod' : (∏ i, c i) = (∏ i,b i)*∏ j,a j := hprod c (fun _ => rfl)
    have hmul : y * (∏ i,c i) = (∏ i,b i)*(y * ∏ j,a j) := by rw [hprod']; ring
    refine mem_image.mpr ⟨y*∏ i,c i,mem_filter.mpr ⟨?_,hmul ▸ dvd_mul_right _ _⟩,?_⟩
    · exact mem_roots.mpr ⟨c,y,hc,hy,by simpa only [hprod',Nat.cast_mul,div_div] using hmax,rfl⟩
    · rw [hmul,Nat.mul_div_cancel_left _ hpos]

/-- The rational torus Weyl sum of the selected roots is the child Weyl sum
at the exact dilated frequency. -/
theorem scalar_marked_group (P : ℝ) (W : ι ⊕ κ → Finset ℕ)
    (H : ∀ i, ∀ p ∈ W i, Nat.Prime p)
    (hs : ∀ i j, ∀ p ∈ W i, p ∈ W j → i=j)
    (hsmall : ∀ a ∈ Fintype.piFinset W, ∀ i, ∀ p ∈ W i, P/((∏ j,a j:ℕ):ℝ)<p)
    (b : ι → ℕ) (hb : ∀ i,b i∈W (.inl i)) (k : ℕ) (θ : WaringLinear.ScalarTorus) :
    WaringLinear.scalarPowerSum ((roots P W).filter (fun n => (∏ i,b i) ∣ n)) k θ =
    WaringLinear.scalarPowerSum (roots (P/((∏ i,b i:ℕ):ℝ)) (fun j=>W (.inr j))) k
      ((∏ i,b i)^k • θ) := by
  rw [WaringLinear.scalar_divide_state,divided_marked_group P W H hs hsmall b hb]

#print axioms divided_marked_group
#print axioms scalar_marked_group

/-- The full decomposition of the parent Weyl sum over a block of marked prime
windows; the scale, remaining window system and frequency are all explicit. -/
theorem scalar_group_decomposition (P : ℝ) (W : ι ⊕ κ → Finset ℕ)
    (H : ∀ i, ∀ p ∈ W i, Nat.Prime p)
    (hs : ∀ i j, ∀ p ∈ W i, p ∈ W j → i=j)
    (hsmall : ∀ a ∈ Fintype.piFinset W, ∀ i, ∀ p ∈ W i, P/((∏ j,a j:ℕ):ℝ)<p)
    (k : ℕ) (θ : WaringLinear.ScalarTorus) :
    WaringLinear.scalarPowerSum (roots P W) k θ =
      ∑ b ∈ Fintype.piFinset (fun i => W (.inl i)),
        WaringLinear.scalarPowerSum (roots (P/((∏ i,b i:ℕ):ℝ)) (fun j=>W (.inr j))) k
          ((∏ i,b i)^k • θ) := by
  let s := roots P W
  let B := Fintype.piFinset (fun i => W (.inl i))
  let get (n : ℕ) : ι ⊕ κ → ℕ := if h : n∈s then (mem_roots.mp h).choose else fun _ => 0
  let mark (n : ℕ) (i : ι) := get n (.inl i)
  have spec (n) (hn : n∈s) : ∃ y, (∀ i, get n i∈W i) ∧ 1 ≤ y ∧
      y ≤ ⌊P / ((∏ i,get n i:ℕ):ℝ)⌋₊ ∧ y * ∏ i,get n i = n := by
    simpa only [get,dif_pos hn] using (mem_roots.mp hn).choose_spec
  have maps (n) (hn : n∈s) : mark n∈B := by
    obtain ⟨_,h,_⟩ := spec n hn
    exact Fintype.mem_piFinset.mpr (fun i => h (.inl i))
  have filt (b) (hb : b∈B) : s.filter (fun n=>mark n = b) = s.filter (fun n=>(∏ i,b i) ∣ n) := by
    ext n
    simp only [mem_filter]
    refine and_congr_right fun hn => ?_
    obtain ⟨y,ha,hy,hmax,he⟩ := spec n hn
    have h := picked_dvd_iff P W H hs hsmall b (Fintype.mem_piFinset.mp hb) (get n) ha y hy hmax
    rw [he] at h
    exact funext_iff.trans h.symm
  let f (n : ℕ) := fourier ((n^k:ℕ):ℤ) θ
  change (∑ n∈s,f n)=_
  rw [←Finset.sum_fiberwise_of_maps_to (s:=s) (t:=B) (g:=mark) maps f]
  apply sum_congr rfl
  intro b hb
  rw [filt b hb]
  exact scalar_marked_group P W H hs hsmall b (Fintype.mem_piFinset.mp hb) k θ

/-- Smallness of the free cofactor is inherited unchanged by every shortened state. -/
theorem child_cofactor_bound (P : ℝ) (W : ι ⊕ κ → Finset ℕ)
    (hsmall : ∀ a ∈ Fintype.piFinset W, ∀ i, ∀ p ∈ W i, P/((∏ j,a j:ℕ):ℝ)<p)
    (b : ι→ℕ) (hb : ∀ i,b i∈W (.inl i)) :
    ∀ a ∈ Fintype.piFinset (fun j=>W (.inr j)), ∀ i, ∀ p ∈ W (.inr i),
      (P/((∏ i,b i:ℕ):ℝ))/((∏ j,a j:ℕ):ℝ)<p := by
  intro a ha i p hp
  let c := Sum.elim b a
  have hc : c∈Fintype.piFinset W := by
    apply Fintype.mem_piFinset.mpr
    rintro (i|j); exacts [hb i,Fintype.mem_piFinset.mp ha j]
  simpa only [split_product, c, Sum.elim_inl, Sum.elim_inr, Nat.cast_mul, div_div]
    using hsmall c hc (.inr i) p hp

/-- The marked support is an actual subset of the smooth numbers whenever the
window primes and the free cofactor fit beneath the prescribed smoothness cutoff. -/
theorem roots_subset_smooth (P R : ℝ) {τ : Type*} [Fintype τ] (W : τ → Finset ℕ)
    (H : ∀ i, ∀ p ∈ W i, Nat.Prime p)
    (hmarks : ∀ i, ∀ p ∈ W i, (p:ℝ) ≤ R)
    (hcofactor : ∀ a ∈ Fintype.piFinset W, P/((∏ i,a i:ℕ):ℝ) ≤ R) :
    roots P W ⊆ Waring.SmoothMoments.smoothNumbers P R := by
  intro n hn
  refine Waring.SmoothMoments.mem_smoothNumbers.mpr ⟨mem_Icc.mp (roots_subset P W H hn),?_⟩
  obtain ⟨a,y,ha,hy,hmax,rfl⟩ := mem_roots.mp hn
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h|h
  · have hf : 0 < ⌊P/((∏ j,a j:ℕ):ℝ)⌋₊ := by omega
    have hyr : (y:ℝ) ≤ P / ((∏ i,a i : ℕ):ℝ) :=
      le_trans (by exact_mod_cast hmax) (Nat.floor_le ((Nat.floor_pos.mp hf).trans' zero_le_one))
    exact (le_trans (by exact_mod_cast Nat.le_of_dvd hy h) hyr).trans (hcofactor a (Fintype.mem_piFinset.mpr ha))
  · obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finset_prod_iff a).mp h
    exact ((H i _ (ha i)).dvd_iff_eq hp.ne_one).mp hi ▸ hmarks i _ (ha i)

#print axioms scalar_group_decomposition
#print axioms roots_subset_smooth

end WaringLinear.MarkedMass

