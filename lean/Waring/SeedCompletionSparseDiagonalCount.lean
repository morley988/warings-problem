import Waring.SeedCompletionSparseDiagonalZero

/-! # Uniform subpower bound for the sparse signed system -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseDiagonal
open AuxiliaryL2Grouping

theorem differenceProduct_size {p J : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (y : Fin (J+1) → ℕ) (hy : ∀i,(y i : ℝ) ≤ P) :
    ((differenceProduct p y).natAbs : ℝ) ≤ P^(p*J) := by
  rw [Nat.cast_natAbs,Int.cast_abs]
  simp only [differenceProduct,differenceKey,Int.cast_prod,Int.cast_sub,
    Int.cast_pow,Int.cast_natCast,Finset.abs_prod]
  calc
    _ ≤ ∏_i : Fin J,P^p := by
      apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
      intro i hi
      have h0 : (y 0 : ℝ)^p ≤ P^p := pow_le_pow_left₀ (by positivity) (hy 0) p
      have h1 : (y i.succ : ℝ)^p ≤ P^p := pow_le_pow_left₀ (by positivity) (hy i.succ) p
      have h0p : 0 ≤ (y 0 : ℝ)^p := by positivity
      have h1p : 0 ≤ (y i.succ : ℝ)^p := by positivity
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    _ = _ := by simp [← pow_mul]

theorem nonzero_divisor_bound (p J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃C : ℝ,0 < C ∧ ∀P : ℝ,1 ≤ P → ∀y : Fin (J+1) → ℕ,
      (∀i,(y i : ℝ) ≤ P) → differenceProduct p y ≠ 0 →
      (((2*(differenceProduct p y).natAbs.divisors.card)^J : ℕ) : ℝ) ≤ C*P^ε := by
  let B : ℝ := (p*J : ℕ)
  let δ := ε/(B+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδB : B*δ ≤ ε := by
    have he : δ*(B+1)=ε := div_mul_cancel₀ ε (by linarith : B+1 ≠ 0)
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := divisor_power_le_rpow J hδ
  refine ⟨(2 : ℝ)^J*D,by positivity,?_⟩
  intro P hP y hy hn
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hsize : ((differenceProduct p y).natAbs : ℝ) ≤ P^B := by
    simpa only [B,Real.rpow_natCast] using differenceProduct_size hPp.le y hy
  calc
    _ = (2 : ℝ)^J*((differenceProduct p y).natAbs.divisors.card : ℝ)^J := by
      push_cast
      rw [mul_pow]
    _ ≤ (2 : ℝ)^J*(D*((differenceProduct p y).natAbs : ℝ)^δ) :=
      mul_le_mul_of_nonneg_left (hdiv _ (Int.natAbs_pos.mpr hn)) (by positivity)
    _ ≤ (2 : ℝ)^J*(D*(P^B)^δ) := by gcongr
    _ = ((2 : ℝ)^J*D)*P^(B*δ) := by rw [← Real.rpow_mul hPp.le]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP hδB) (by positivity)

def nonzeroSignedSolutions (p J : ℕ) (A : Finset ℕ) :
    Finset ((Fin (J+1) → ℕ) × (Fin (J+1) → ℕ)) :=
  (signedSolutions p J A).filter (fun xy => differenceProduct p xy.2 ≠ 0)

theorem nonzero_signed_solutions_card_le {p J : ℕ} (hp : 0 < p) (hJ : 2 ≤ J)
    (A : Finset ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀y∈finiteTuples A (J+1),differenceProduct p y ≠ 0 →
      (((2*(differenceProduct p y).natAbs.divisors.card)^J : ℕ) : ℝ) ≤ D) :
    ((nonzeroSignedSolutions p J A).card : ℝ) ≤ (A.card : ℝ)^(J+1)*D := by
  classical
  let E := nonzeroSignedSolutions p J A
  have hmap : Set.MapsTo
      (fun xy : (Fin (J+1) → ℕ) × (Fin (J+1) → ℕ) => xy.2)
      E (finiteTuples A (J+1)) := by
    intro xy hxy
    exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).1).2
  have hfiber (y : Fin (J+1) → ℕ) (hy : y∈finiteTuples A (J+1)) :
      ((E.filter (fun xy => xy.2=y)).card : ℝ) ≤ D := by
    let F := E.filter (fun xy => xy.2=y)
    by_cases hzero : differenceProduct p y=0
    · have hF : F=∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro xy hxy
        have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).2
        rw [(Finset.mem_filter.mp hxy).2,hzero] at hn
        exact hn rfl
      change (F.card : ℝ) ≤ D
      rw [hF,Finset.card_empty,Nat.cast_zero]
      exact hD
    · have hi : Set.InjOn
          (fun xy : (Fin (J+1) → ℕ) × (Fin (J+1) → ℕ) => xy.1) F := by
        intro x hx z hz he
        exact Prod.ext he ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm)
      have hc : (F.image Prod.fst).card ≤ (2*(differenceProduct p y).natAbs.divisors.card)^J := by
        apply nonzero_signed_fiber_card_le hJ hp _ y hzero
        intro x hx r hr hrJ
        obtain ⟨xy,hxy,rfl⟩ := Finset.mem_image.mp hx
        have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).1).2 r hr hrJ
        rwa [(Finset.mem_filter.mp hxy).2] at hs
      change (F.card : ℝ) ≤ D
      rw [← Finset.card_image_of_injOn hi]
      exact (show ((F.image Prod.fst).card : ℝ) ≤
        (((2*(differenceProduct p y).natAbs.divisors.card)^J : ℕ) : ℝ) by exact_mod_cast hc).trans
          (hbound y hy hzero)
  change (E.card : ℝ) ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap,Nat.cast_sum]
  calc
    _ ≤ ∑_y∈finiteTuples A (J+1),D := Finset.sum_le_sum hfiber
    _ = _ := by simp [finiteTuples,Fintype.card_piFinset]

theorem signed_solutions_subpower (p J : ℕ) (hp : 0 < p) (hJ : 2 ≤ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∃C : ℝ,0 < C ∧ ∀P : ℝ,1 ≤ P → ∀A : Finset ℕ,
      (∀a∈A,(a : ℝ) ≤ P) → (A.card : ℝ) ≤ P →
      ((signedSolutions p J A).card : ℝ) ≤ C*P^((J+1 : ℕ)+ε) := by
  obtain ⟨D,hD,hdiv⟩ := nonzero_divisor_bound p J hε
  let C₀ : ℝ := (J*J^J : ℕ)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀+D,by linarith,?_⟩
  intro P hP A hA hcard
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hn := nonzero_signed_solutions_card_le hp hJ A
    (show 0 ≤ D*P^ε by positivity) (by
      intro y hy hne
      exact hdiv P hP y (fun i => hA _ (Fintype.mem_piFinset.mp hy i)) hne)
  have hz : ((zeroSignedSolutions p J A).card : ℝ) ≤ C₀*(A.card : ℝ)^(J+1) := by
    dsimp [C₀]
    exact_mod_cast zero_signed_solutions_card_le (J := J) hp A
  have hsplit : (signedSolutions p J A).card=
      (zeroSignedSolutions p J A).card+(nonzeroSignedSolutions p J A).card :=
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := signedSolutions p J A) (fun xy => differenceProduct p xy.2=0)).symm
  rw [hsplit,Nat.cast_add]
  have hpowers : P^(J+1)*P^ε=P^((J+1 : ℕ)+ε) := by
    rw [← Real.rpow_natCast P (J+1),← Real.rpow_add hPp]
  calc
    _ ≤ C₀*(A.card : ℝ)^(J+1)+(A.card : ℝ)^(J+1)*(D*P^ε) := add_le_add hz hn
    _ ≤ C₀*P^(J+1)+P^(J+1)*(D*P^ε) := by gcongr
    _ ≤ C₀*(P^(J+1)*P^ε)+D*(P^(J+1)*P^ε) := by
      have he := Real.one_le_rpow hP hε.le
      have hb := mul_le_mul_of_nonneg_left he (show 0 ≤ C₀*P^(J+1) by positivity)
      nlinarith only [hb]
    _ = _ := by rw [hpowers]; ring

#print axioms signed_solutions_subpower
end Waring.SeedCompletionSparseDiagonal
