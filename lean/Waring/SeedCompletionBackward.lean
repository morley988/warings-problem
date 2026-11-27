import Waring.DifferencePolynomials
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Exact backward differencing of congruent pairs

These are the arithmetic changes of variables in Wooley's successive
differencing step: `x = z+z'`, `h = (z-z')/w^k`, followed by doubling the
old heights and the smooth variables. The phase is the project's actual
`modifiedCenteredPower`; no moment inequality is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Waring.SeedCompletionBackward
open Differences

/-- Scale every height while retaining its coefficient. -/
def scaleHeights (c : ℝ) (params : List (ℝ × ℝ)) : List (ℝ × ℝ) :=
  params.map (fun hm => (c * hm.1, hm.2))

/-- Simultaneously scaling the central variable and every old height scales
the whole degree-k difference polynomial by the kth power. -/
theorem modifiedCenteredPower_scale (k : ℕ) (c : ℝ)
    (params : List (ℝ × ℝ)) (z : ℝ) :
    modifiedCenteredPower k (scaleHeights c params) (c * z) =
      c ^ k * modifiedCenteredPower k params z := by
  induction params generalizing z with
  | nil => simp [modifiedCenteredPower, scaleHeights, mul_pow]
  | cons hm rest ih =>
    simp only [scaleHeights, List.map_cons, modifiedCenteredPower]
    change (modifiedCenteredPower k (scaleHeights c rest) (c*z+(c*hm.1)*hm.2^k) -
      modifiedCenteredPower k (scaleHeights c rest) (c*z-(c*hm.1)*hm.2^k)) / hm.2^k = _
    rw [show c*z+(c*hm.1)*hm.2^k = c*(z+hm.1*hm.2^k) by ring,
      show c*z-(c*hm.1)*hm.2^k = c*(z-hm.1*hm.2^k) by ring, ih, ih]
    ring

/-- The congruent pair gives exactly the next centered-difference phase.
The identity also holds with totalized division at a zero coefficient. -/
theorem backward_phase_identity (k : ℕ) (params : List (ℝ × ℝ))
    (z z' h w : ℝ) (hdiff : z - z' = h * w ^ k) :
    modifiedCenteredPower k ((h,w) :: scaleHeights 2 params) (z+z') =
      (2 : ℝ)^k *
        (modifiedCenteredPower k params z - modifiedCenteredPower k params z') / w^k := by
  simp only [modifiedCenteredPower]
  rw [show z+z'+h*w^k = 2*z by linarith [hdiff],
    show z+z'-h*w^k = 2*z' by linarith [hdiff],
    modifiedCenteredPower_scale, modifiedCenteredPower_scale]
  ring

/-- A literal original collision becomes a literal next-stage equation;
the smooth contribution is multiplied by exactly `2^k`. -/
theorem backward_solution (k : ℕ) (params : List (ℝ × ℝ))
    (z z' h w U V : ℝ) (hw : w ≠ 0) (hdiff : z - z' = h * w ^ k)
    (heq : modifiedCenteredPower k params z + w^k*U =
      modifiedCenteredPower k params z' + w^k*V) :
    modifiedCenteredPower k ((h,w) :: scaleHeights 2 params) (z+z') +
      (2 : ℝ)^k*U = (2 : ℝ)^k*V := by
  rw [backward_phase_identity k params z z' h w hdiff]
  have hq : w^k ≠ 0 := pow_ne_zero k hw
  field_simp
  linear_combination heq

/-- Doubling the smooth tuple has precisely the factor appearing above. -/
theorem doubled_power_sum (k s : ℕ) (u : Fin s → ℤ) :
    (∑ i, (2*u i)^k) = (2 : ℤ)^k * ∑ i, (u i)^k := by
  simp_rw [mul_pow]
  exact (Finset.mul_sum _ _ _).symm

/-- The integer pair encoding retains the sum and the exact congruence
quotient. -/
def pairEncoding (q : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1+p.2, (p.1-p.2)/q)

theorem pairEncoding_difference {q : ℤ} {p : ℤ × ℤ} (hp : q ∣ p.1-p.2) :
    (pairEncoding q p).2 * q = p.1-p.2 := by
  exact Int.ediv_mul_cancel hp

/-- Congruent pairs are recovered uniquely from the encoded data. -/
theorem pairEncoding_injective (q : ℤ) :
    Set.InjOn (pairEncoding q) {p : ℤ × ℤ | q ∣ p.1-p.2} := by
  intro p hp r hr heq
  have hsum : p.1+p.2 = r.1+r.2 := congrArg Prod.fst heq
  have hquot : (pairEncoding q p).2 = (pairEncoding q r).2 := congrArg Prod.snd heq
  have hdiff : p.1-p.2 = r.1-r.2 := by
    rw [← pairEncoding_difference hp, ← pairEncoding_difference hr, hquot]
  apply Prod.ext <;> linarith

/-- Positive ordered pairs in `[1,P]` give the literal enlarged center
interval and the shortened positive-height interval. -/
theorem pairEncoding_bounds {q P z z' : ℤ} (hq : 0 < q)
    (_hz : 1 ≤ z) (hzP : z ≤ P) (hz' : 1 ≤ z') (_hz'P : z' ≤ P)
    (horder : z' < z) (hdiv : q ∣ z-z') :
    2 ≤ (pairEncoding q (z,z')).1 ∧ (pairEncoding q (z,z')).1 ≤ 2*P ∧
      1 ≤ (pairEncoding q (z,z')).2 ∧ (pairEncoding q (z,z')).2 ≤ P/q := by
  change 2 ≤ z+z' ∧ z+z' ≤ 2*P ∧ 1 ≤ (z-z')/q ∧ (z-z')/q ≤ P/q
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have hp : 0 < (z-z')/q := by
      have hprod : 0 < ((z-z')/q)*q := by
        rw [Int.ediv_mul_cancel hdiv]
        exact sub_pos.mpr horder
      exact pos_of_mul_pos_left hprod hq.le
    omega
  · exact Int.ediv_le_ediv hq (by linarith)

/-- The literal fixed-parameter collision count after common-residue
conditioning. The smooth tuple domain and its power sum remain explicit. -/
def stepSolutions {ι : Type*} (k : ℕ) (params : List (ℝ × ℝ)) (w : ℤ)
    (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ) : Finset ((ℤ × ι) × (ℤ × ι)) := by
  classical
  exact ((Z ×ˢ B) ×ˢ (Z ×ˢ B)).filter fun p =>
    w^k ∣ p.1.1-p.2.1 ∧
      modifiedCenteredPower k params p.1.1 + (w : ℝ)^k*U p.1.2 =
        modifiedCenteredPower k params p.2.1 + (w : ℝ)^k*U p.2.2

def positiveStepSolutions {ι : Type*} (k : ℕ) (params : List (ℝ × ℝ)) (w : ℤ)
    (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ) : Finset ((ℤ × ι) × (ℤ × ι)) := by
  classical
  exact (stepSolutions k params w Z B U).filter fun p => p.2.1 < p.1.1

/-- The actual next-stage equation on its enlarged center interval and
shortened positive height interval. The old heights and smooth powers have
the exact factors of two from the source change of variables. -/
def nextStepSolutions {ι : Type*} (k : ℕ) (params : List (ℝ × ℝ)) (w P : ℤ)
    (B : Finset ι) (U : ι → ℝ) : Finset ((ℤ × ℤ) × (ι × ι)) := by
  classical
  exact ((Finset.Icc 2 (2*P) ×ˢ Finset.Icc 1 (P/w^k)) ×ˢ (B ×ˢ B)).filter fun p =>
    modifiedCenteredPower k (((p.1.2 : ℝ),(w : ℝ)) :: scaleHeights 2 params) p.1.1 +
      (2 : ℝ)^k*U p.2.1 = (2 : ℝ)^k*U p.2.2

def stepEncoding {ι : Type*} (q : ℤ) (p : (ℤ × ι) × (ℤ × ι)) :
    (ℤ × ℤ) × (ι × ι) :=
  (pairEncoding q (p.1.1,p.2.1), (p.1.2,p.2.2))

theorem stepEncoding_injective {ι : Type*} (q : ℤ) :
    Set.InjOn (stepEncoding (ι := ι) q)
      {p : (ℤ × ι) × (ℤ × ι) | q ∣ p.1.1-p.2.1} := by
  intro p hp r hr heq
  have hz : (p.1.1,p.2.1) = (r.1.1,r.2.1) :=
    pairEncoding_injective q hp hr (congrArg Prod.fst heq)
  have hu : (p.1.2,p.2.2) = (r.1.2,r.2.2) := congrArg Prod.snd heq
  have hz1 : p.1.1 = r.1.1 := congrArg (fun t : ℤ × ℤ => t.1) hz
  have hz2 : p.2.1 = r.2.1 := congrArg (fun t : ℤ × ℤ => t.2) hz
  have hu1 : p.1.2 = r.1.2 := congrArg (fun t : ι × ι => t.1) hu
  have hu2 : p.2.2 = r.2.2 := congrArg (fun t : ι × ι => t.2) hu
  exact Prod.ext (Prod.ext hz1 hu1) (Prod.ext hz2 hu2)

/-- Every positively ordered original collision injects into the literal
next-stage solution set. This is a count inequality, not a presumed analytic
efficient-differencing estimate. -/
theorem positive_step_card_le_next {ι : Type*} (k : ℕ)
    (params : List (ℝ × ℝ)) (w P : ℤ) (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ)
    (hw : 0 < w) (hZ : Z ⊆ Finset.Icc 1 P) :
    (positiveStepSolutions k params w Z B U).card ≤
      (nextStepSolutions k params w P B U).card := by
  classical
  apply Finset.card_le_card_of_injOn (stepEncoding (w^k))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,horder⟩
    rcases Finset.mem_filter.mp hp with ⟨hdom,hdiv,heq⟩
    rcases Finset.mem_product.mp hdom with ⟨hleft,hright⟩
    rcases Finset.mem_product.mp hleft with ⟨hz,hU⟩
    rcases Finset.mem_product.mp hright with ⟨hz',hV⟩
    rcases Finset.mem_Icc.mp (hZ hz) with ⟨hz1,hzP⟩
    rcases Finset.mem_Icc.mp (hZ hz') with ⟨hz'1,hz'P⟩
    have hb := pairEncoding_bounds (pow_pos hw k) hz1 hzP hz'1 hz'P horder hdiv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb.1,hb.2.1⟩,
        Finset.mem_Icc.mpr ⟨hb.2.2.1,hb.2.2.2⟩⟩,
        Finset.mem_product.mpr ⟨hU,hV⟩⟩, ?_⟩
    have hdiff : (p.1.1 : ℝ) - p.2.1 =
        (((p.1.1-p.2.1)/w^k : ℤ) : ℝ) * (w : ℝ)^k := by
      exact_mod_cast (Int.ediv_mul_cancel hdiv).symm
    have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
    simpa only [stepEncoding,pairEncoding,Int.cast_add] using
      backward_solution k params p.1.1 p.2.1 (((p.1.1-p.2.1)/w^k : ℤ) : ℝ)
        (w : ℝ) (U p.1.2) (U p.2.2) hwR hdiff heq
  · intro p hp r hr heq
    apply stepEncoding_injective (w^k) _ _ heq
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1

/-- A symmetric collision set is its diagonal plus twice either strict
ordering. The two orientations are paired by swapping both full points. -/
theorem symmetric_card_split {α : Type*} (S : Finset (α × α)) (z : α → ℤ)
    (hswap : ∀ p ∈ S, (p.2,p.1) ∈ S) :
    S.card = (S.filter (fun p => z p.1 = z p.2)).card +
      2*(S.filter (fun p => z p.2 < z p.1)).card := by
  classical
  let D := S.filter (fun p => z p.1 = z p.2)
  let F := S.filter (fun p => z p.2 < z p.1)
  let G := S.filter (fun p => z p.1 < z p.2)
  have hS : S = D ∪ (F ∪ G) := by
    ext p
    simp only [D,F,G,Finset.mem_filter,Finset.mem_union]
    constructor
    · intro hp
      rcases lt_trichotomy (z p.1) (z p.2) with hlt | heq | hgt
      · exact Or.inr (Or.inr ⟨hp,hlt⟩)
      · exact Or.inl ⟨hp,heq⟩
      · exact Or.inr (Or.inl ⟨hp,hgt⟩)
    · rintro (⟨hp,_⟩ | ⟨hp,_⟩ | ⟨hp,_⟩) <;> exact hp
  have hFG : Disjoint F G := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_gt (Finset.mem_filter.mp hp).2) (Finset.mem_filter.mp hq).2
  have hD : Disjoint D (F ∪ G) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have heq := (Finset.mem_filter.mp hp).2
    rcases Finset.mem_union.mp hq with hf | hg
    · have hlt := (Finset.mem_filter.mp hf).2
      omega
    · have hlt := (Finset.mem_filter.mp hg).2
      omega
  have hGF : G.card = F.card := by
    apply Finset.card_bij (fun p _ => (p.2,p.1))
    · intro p hp
      exact Finset.mem_filter.mpr ⟨hswap p (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2⟩
    · intro p hp r hr heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro p hp
      refine ⟨(p.2,p.1), Finset.mem_filter.mpr
        ⟨hswap p (Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2⟩, rfl⟩
  calc
    S.card = D.card + (F.card+G.card) := by
      rw [hS,Finset.card_union_of_disjoint hD,Finset.card_union_of_disjoint hFG]
    _ = D.card+2*F.card := by rw [hGF]; omega

def diagonalStepSolutions {ι : Type*} (k : ℕ) (params : List (ℝ × ℝ)) (w : ℤ)
    (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ) : Finset ((ℤ × ι) × (ℤ × ι)) := by
  classical
  exact (stepSolutions k params w Z B U).filter fun p => p.1.1 = p.2.1

theorem stepSolutions_swap {ι : Type*} (k : ℕ) (params : List (ℝ × ℝ)) (w : ℤ)
    (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ)
    {p : (ℤ × ι) × (ℤ × ι)} (hp : p ∈ stepSolutions k params w Z B U) :
    (p.2,p.1) ∈ stepSolutions k params w Z B U := by
  classical
  rcases Finset.mem_filter.mp hp with ⟨hdom,hdiv,heq⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨(Finset.mem_product.mp hdom).2,(Finset.mem_product.mp hdom).1⟩,?_,heq.symm⟩
  simpa only [neg_sub] using dvd_neg.mpr hdiv

/-- The full congruent collision count has the exact source diagonal and
at most twice the literal next-stage count. -/
theorem step_card_le_diagonal_add_next {ι : Type*} (k : ℕ)
    (params : List (ℝ × ℝ)) (w P : ℤ) (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ)
    (hw : 0 < w) (hZ : Z ⊆ Finset.Icc 1 P) :
    (stepSolutions k params w Z B U).card ≤
      (diagonalStepSolutions k params w Z B U).card +
        2*(nextStepSolutions k params w P B U).card := by
  classical
  have heq := symmetric_card_split (stepSolutions k params w Z B U) Prod.fst
    (fun _ hp => stepSolutions_swap k params w Z B U hp)
  change (stepSolutions k params w Z B U).card =
    (diagonalStepSolutions k params w Z B U).card +
      2*(positiveStepSolutions k params w Z B U).card at heq
  rw [heq]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (positive_step_card_le_next k params w P Z B U hw hZ)) _

#print axioms modifiedCenteredPower_scale
#print axioms backward_solution
#print axioms pairEncoding_injective
#print axioms pairEncoding_bounds
#print axioms positive_step_card_le_next
#print axioms step_card_le_diagonal_add_next

end Waring.SeedCompletionBackward
