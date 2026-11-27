import Waring.SeedCompletionCurveElimination
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Short and long edges in a monotone lattice-point sequence

A bounded multiplicity for each positive integer edge vector and a bound
for total coordinate variation give the uniform two-thirds power estimate.
All counting statements concern the literal finite sequence.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionCurveLattice

def edge {n : ℕ} (x y : Fin (n+1) → ℕ) (i : Fin n) : ℕ×ℕ :=
  (x i.succ-x i.castSucc, y i.succ-y i.castSucc)

theorem telescope {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ i : Fin n, (f i.succ-f i.castSucc)) = f (Fin.last n)-f 0 := by
  have hs := Fin.sum_univ_succ f
  have ht := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

theorem edge_pos {n : ℕ} (x y : Fin (n+1) → ℕ)
    (hx : StrictMono x) (hy : StrictMono y) (i : Fin n) :
    0 < (edge x y i).1 ∧ 0 < (edge x y i).2 :=
  ⟨Nat.sub_pos_of_lt (hx i.castSucc_lt_succ),
    Nat.sub_pos_of_lt (hy i.castSucc_lt_succ)⟩

theorem total_edge_length_le {n : ℕ} (x y : Fin (n+1) → ℕ)
    (hx : StrictMono x) (hy : StrictMono y) (P : ℝ)
    (hbox : ∀ i, (x i : ℝ) ≤ P ∧ (y i : ℝ) ≤ P) :
    (∑ i : Fin n, (((edge x y i).1 : ℝ)+(edge x y i).2)) ≤ 2*P := by
  have hedge (i : Fin n) :
      (((edge x y i).1 : ℝ)+(edge x y i).2) =
      ((x i.succ : ℝ)-x i.castSucc)+((y i.succ : ℝ)-y i.castSucc) := by
    dsimp [edge]
    rw [Nat.cast_sub (hx.monotone i.castSucc_le_succ),
      Nat.cast_sub (hy.monotone i.castSucc_le_succ)]
  simp_rw [hedge]
  rw [Finset.sum_add_distrib,telescope (fun i => (x i : ℝ)),
    telescope (fun i => (y i : ℝ))]
  have hx0 : (0 : ℝ) ≤ x (0 : Fin (n+1)) := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ y (0 : Fin (n+1)) := Nat.cast_nonneg _
  have hb := hbox (Fin.last n)
  linarith

/-- Exact short/long edge split, before choosing the cutoff. -/
theorem monotone_sequence_cutoff {n : ℕ} (x y : Fin (n+1) → ℕ)
    (hx : StrictMono x) (hy : StrictMono y) (P : ℝ)
    (hbox : ∀ i, (x i : ℝ) ≤ P ∧ (y i : ℝ) ≤ P)
    (B T : ℕ) (hT : 0 < T)
    (hcapacity : ∀ a b : ℕ, 0 < a → 0 < b →
      ((Finset.univ : Finset (Fin n)).filter (fun i => edge x y i=(a,b))).card ≤ B) :
    (n+1 : ℝ) ≤ (B : ℝ)*(T : ℝ)^2 + 2*P/(T : ℝ)+1 := by
  classical
  let short := (Finset.univ : Finset (Fin n)).filter
    (fun i => (edge x y i).1+(edge x y i).2 ≤ T)
  let long := (Finset.univ : Finset (Fin n)).filter
    (fun i => ¬(edge x y i).1+(edge x y i).2 ≤ T)
  let box := (Finset.Icc 1 T).product (Finset.Icc 1 T)
  have hmaps : ∀ i ∈ short, edge x y i ∈ box := by
    intro i hi
    have hlen := (Finset.mem_filter.mp hi).2
    have hpos := edge_pos x y hx hy i
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hpos.1,by omega⟩,
      Finset.mem_Icc.mpr ⟨hpos.2,by omega⟩⟩
  have hshort : short.card ≤ B*T^2 := by
    calc
      short.card = ∑ v ∈ box, (short.filter (fun i => edge x y i=v)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ _v ∈ box, B := by
        apply Finset.sum_le_sum
        intro v hv
        have hvp := Finset.mem_product.mp hv
        have hf : short.filter (fun i => edge x y i=v) ⊆
            (Finset.univ : Finset (Fin n)).filter (fun i => edge x y i=v) := by
          intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,(Finset.mem_filter.mp hi).2⟩
        exact (Finset.card_le_card hf).trans
          (hcapacity v.1 v.2 (Finset.mem_Icc.mp hvp.1).1 (Finset.mem_Icc.mp hvp.2).1)
      _ = B*T^2 := by simp [box,Finset.card_product,Nat.card_Icc]; ring
  have hlong : (long.card : ℝ)*(T : ℝ) ≤ 2*P := by
    calc
      (long.card : ℝ)*(T : ℝ) = ∑ _i ∈ long, (T : ℝ) := by simp
      _ ≤ ∑ i ∈ long, (((edge x y i).1 : ℝ)+(edge x y i).2) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh : T ≤ (edge x y i).1+(edge x y i).2 :=
          (Nat.lt_of_not_ge (Finset.mem_filter.mp hi).2).le
        exact_mod_cast hh
      _ ≤ ∑ i : Fin n, (((edge x y i).1 : ℝ)+(edge x y i).2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
      _ ≤ 2*P := total_edge_length_le x y hx hy P hbox
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hlong' : (long.card : ℝ) ≤ 2*P/(T : ℝ) := (le_div_iff₀ hTR).mpr hlong
  have hshort' : (short.card : ℝ) ≤ (B : ℝ)*(T : ℝ)^2 := by exact_mod_cast hshort
  have hcards : short.card+long.card=n := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := Finset.univ) (fun i : Fin n => (edge x y i).1+(edge x y i).2 ≤ T))
  have hcR : (short.card : ℝ)+(long.card : ℝ)=n := by exact_mod_cast hcards
  linarith

/-- Choosing the cube-root cutoff gives a coefficient-free two-thirds
power bound from the actual edge-vector capacity. -/
theorem monotone_sequence_card_bound {n : ℕ} (x y : Fin (n+1) → ℕ)
    (hx : StrictMono x) (hy : StrictMono y) (P : ℝ) (hP : 1 ≤ P)
    (hbox : ∀ i, (x i : ℝ) ≤ P ∧ (y i : ℝ) ≤ P)
    (B : ℕ)
    (hcapacity : ∀ a b : ℕ, 0 < a → 0 < b →
      ((Finset.univ : Finset (Fin n)).filter (fun i => edge x y i=(a,b))).card ≤ B) :
    (n+1 : ℝ) ≤ (4*(B : ℝ)+3)*P^(2/3 : ℝ) := by
  let R := P^(1/3 : ℝ)
  let T := ⌈R⌉₊
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR : 1 ≤ R := Real.one_le_rpow hP (by norm_num)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hT : 0 < T := Nat.ceil_pos.mpr hRpos
  have hRT : R ≤ (T : ℝ) := Nat.le_ceil R
  have hTupper : (T : ℝ) ≤ 2*R := by
    have h := Nat.ceil_lt_add_one hRpos.le
    dsimp [T]
    linarith
  have hRtwo : R^2=P^(2/3 : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast hPpos.le]
    norm_num
  have hPR : P/R=P^(2/3 : ℝ) := by
    apply (div_eq_iff hRpos.ne').mpr
    dsimp [R]
    rw [← Real.rpow_add hPpos]
    norm_num
  have hshort : (B : ℝ)*(T : ℝ)^2 ≤ 4*(B : ℝ)*P^(2/3 : ℝ) := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg T) hTupper 2
    rw [mul_pow,hRtwo] at hsq
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg B)]
  have hlong : 2*P/(T : ℝ) ≤ 2*P^(2/3 : ℝ) := by
    calc
      _ ≤ 2*P/R := div_le_div_of_nonneg_left (by positivity) hRpos hRT
      _ = _ := by rw [mul_div_assoc,hPR]
  have hsmall : 1 ≤ P^(2/3 : ℝ) := Real.one_le_rpow hP (by norm_num)
  have hbound := monotone_sequence_cutoff x y hx hy P hbox B T hT hcapacity
  nlinarith

/-- A finite monotone set with bounded translated self-intersections has a
uniform two-thirds power count. -/
theorem monotone_set_card_bound (S : Finset (ℕ×ℕ)) (P : ℝ) (hP : 1 ≤ P)
    (hbox : ∀ z ∈ S, (z.1 : ℝ) ≤ P ∧ (z.2 : ℝ) ≤ P)
    (hinj : Set.InjOn Prod.fst (↑S : Set (ℕ×ℕ)))
    (horder : ∀ z ∈ S, ∀ w ∈ S, z.1 < w.1 → z.2 < w.2)
    (B : ℕ)
    (hcapacity : ∀ a b : ℕ, 0 < a → 0 < b →
      (S.filter (fun z => (z.1+a,z.2+b) ∈ S)).card ≤ B) :
    (S.card : ℝ) ≤ (4*(B : ℝ)+3)*P^(2/3 : ℝ) := by
  classical
  by_cases hS : S.card=0
  · rw [hS,Nat.cast_zero]
    positivity
  let n := S.card-1
  have hn : S.card=n+1 := by dsimp [n]; omega
  let X := S.image Prod.fst
  have hX : X.card=n+1 := (Finset.card_image_of_injOn hinj).trans hn
  let e := X.orderEmbOfFin hX
  have hexists (i : Fin (n+1)) : ∃ z ∈ S, z.1=e i :=
    Finset.mem_image.mp (X.orderEmbOfFin_mem hX i)
  choose z hz hzx using hexists
  let x : Fin (n+1) → ℕ := fun i => (z i).1
  let y : Fin (n+1) → ℕ := fun i => (z i).2
  have hx : StrictMono x := by
    intro i j hij
    dsimp [x]
    rw [hzx,hzx]
    exact e.strictMono hij
  have hy : StrictMono y := by
    intro i j hij
    exact horder (z i) (hz i) (z j) (hz j) (hx hij)
  have hcap : ∀ a b : ℕ, 0 < a → 0 < b →
      ((Finset.univ : Finset (Fin n)).filter (fun i => edge x y i=(a,b))).card ≤ B := by
    intro a b ha hb
    let U := (Finset.univ : Finset (Fin n)).filter (fun i => edge x y i=(a,b))
    let f : Fin n → ℕ×ℕ := fun i => z i.castSucc
    have hf : Function.Injective f := by
      intro i j hij
      have hh : x i.castSucc=x j.castSucc := congrArg Prod.fst hij
      exact Fin.castSucc_inj.mp (hx.injective hh)
    have hsub : U.image f ⊆ S.filter (fun w => (w.1+a,w.2+b) ∈ S) := by
      intro w hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      have hdelta := (Finset.mem_filter.mp hi).2
      have hdx : x i.succ-x i.castSucc=a := congrArg Prod.fst hdelta
      have hdy : y i.succ-y i.castSucc=b := congrArg Prod.snd hdelta
      have hmx := hx.monotone i.castSucc_le_succ
      have hmy := hy.monotone i.castSucc_le_succ
      have hnext : (f i).1+a=(z i.succ).1 ∧ (f i).2+b=(z i.succ).2 := by
        change x i.castSucc+a=x i.succ ∧ y i.castSucc+b=y i.succ
        constructor <;> omega
      apply Finset.mem_filter.mpr
      refine ⟨hz i.castSucc,?_⟩
      rw [hnext.1,hnext.2]
      exact hz i.succ
    calc
      U.card = (U.image f).card := (Finset.card_image_of_injective _ hf).symm
      _ ≤ (S.filter (fun w => (w.1+a,w.2+b) ∈ S)).card := Finset.card_le_card hsub
      _ ≤ B := hcapacity a b ha hb
  have hb := monotone_sequence_card_bound x y hx hy P hP
    (fun i => hbox (z i) (hz i)) B hcap
  simpa only [hn,Nat.cast_add,Nat.cast_one] using hb

#print axioms monotone_sequence_cutoff
#print axioms monotone_sequence_card_bound
#print axioms monotone_set_card_bound
end Waring.SeedCompletionCurveLattice
