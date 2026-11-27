import Waring.SeedCompletionNinthDouble

/-!
# Genuine j=2 auxiliary second moment in degree nine

Frequency grouping keeps exactly the heights and center. The remaining
coefficient collisions are split by equality of their full center
polynomials, giving the diagonal term and a bounded-root error.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthDoubleCount
open SeedCompletionNinthDouble AuxiliaryL2Grouping PolicyCompletionCongruence

abbrev Index := Pair × Pair × ℕ
abbrev CenterIndex := Pair × Pair × Pair × ℕ

def indexPhase (x : Index) : ℤ := (doublePhase x.1 x.2.1 x.2.2 : ℤ)
def divisorKey (x : Index) : Fin 3 → ℕ := ![x.1.1,x.1.2,x.2.2]

def domain (H B : Finset Pair) (Z : Finset ℕ) : Finset Index := H ×ˢ (B ×ˢ Z)
def equalCenterSolutions (H B : Finset Pair) (Z : Finset ℕ) : Finset CenterIndex :=
  (H ×ˢ (B ×ˢ (B ×ˢ Z))).filter
    (fun x => doublePhase x.1 x.2.1 x.2.2.2=doublePhase x.1 x.2.2.1 x.2.2.2)

theorem divisorKey_dvd (x : Index) (i : Fin 3) : (divisorKey x i : ℤ) ∣ indexPhase x := by
  fin_cases i
  · simpa only [divisorKey,Matrix.cons_val_zero,indexPhase] using
      (show (x.1.1 : ℤ) ∣ (doublePhase x.1 x.2.1 x.2.2 : ℤ) by
        exact_mod_cast firstHeight_dvd x.1 x.2.1 x.2.2)
  · simpa only [divisorKey,Matrix.cons_val_one,Matrix.cons_val_zero,indexPhase] using
      (show (x.1.2 : ℤ) ∣ (doublePhase x.1 x.2.1 x.2.2 : ℤ) by
        exact_mod_cast secondHeight_dvd x.1 x.2.1 x.2.2)
  · simpa only [divisorKey,Matrix.cons_val_two,Matrix.cons_val_zero,indexPhase] using
      (show (x.2.2 : ℤ) ∣ (doublePhase x.1 x.2.1 x.2.2 : ℤ) by
        exact_mod_cast center_dvd x.1 x.2.1 x.2.2)

theorem divisorKey_eq_iff (x y : Index) :
    divisorKey x=divisorKey y ↔ x.1=y.1 ∧ x.2.2=y.2.2 := by
  constructor
  · intro he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    change x.1.1=y.1.1 at h0
    change x.1.2=y.1.2 at h1
    change x.2.2=y.2.2 at h2
    exact ⟨Prod.ext h0 h1,h2⟩
  · rintro ⟨hh,hz⟩
    simp only [divisorKey,hh,hz]

/-- Finite counting of a Cartesian fiber, with its actual predicate. -/
theorem card_filter_product {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (p : ι → κ → Prop) [DecidablePred (fun x : ι × κ => p x.1 x.2)]
    [∀ a, DecidablePred (p a)] :
    ((A ×ˢ B).filter (fun x => p x.1 x.2)).card =
      ∑ a ∈ A, (B.filter (p a)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]

theorem equalCenterSolutions_card (H B : Finset Pair) (Z : Finset ℕ) :
    (equalCenterSolutions H B Z).card =
      ∑ h ∈ H, ∑ m ∈ B, ∑ n ∈ B,
        (Z.filter (fun z => doublePhase h m z=doublePhase h n z)).card := by
  classical
  simp only [equalCenterSolutions,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]

def centerCode (x : CenterIndex) : Index × Index :=
  ((x.1,x.2.1,x.2.2.2),(x.1,x.2.2.1,x.2.2.2))

theorem centerCode_injective : Function.Injective centerCode := by
  rintro ⟨h,m,n,z⟩ ⟨h',m',n',z'⟩ he
  simp only [centerCode,Prod.mk.injEq] at he ⊢
  tauto

/-- Exact same-height, same-center collision count after divisor grouping. -/
theorem sameClass_card_eq (H B : Finset Pair) (Z : Finset ℕ) :
    (sameClassCollisions (domain H B Z) indexPhase divisorKey).card =
      (equalCenterSolutions H B Z).card := by
  classical
  have heq : sameClassCollisions (domain H B Z) indexPhase divisorKey =
      (equalCenterSolutions H B Z).image centerCode := by
    ext p
    rcases p with ⟨⟨h,m,z⟩,⟨h',n,z'⟩⟩
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hkey⟩
      rcases (divisorKey_eq_iff _ _).mp hkey with ⟨hh,hz⟩
      dsimp only at hh hz
      subst h'
      subst z'
      rcases Finset.mem_filter.mp hp with ⟨hp,hfreq⟩
      rcases Finset.mem_product.mp hp with ⟨hx,hy⟩
      rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
      rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
      have hn := (Finset.mem_product.mp (Finset.mem_product.mp hy).2).1
      apply Finset.mem_image.mpr
      refine ⟨(h,m,n,z),Finset.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
      · exact Finset.mem_product.mpr ⟨hh,Finset.mem_product.mpr
          ⟨hm,Finset.mem_product.mpr ⟨hn,hz⟩⟩⟩
      · dsimp only [indexPhase] at hfreq
        exact_mod_cast hfreq
    · intro hp
      obtain ⟨⟨g,a,b,t⟩,hgabt,he⟩ := Finset.mem_image.mp hp
      rcases Finset.mem_filter.mp hgabt with ⟨hgabt,hfreq⟩
      rcases Finset.mem_product.mp hgabt with ⟨hg,habt⟩
      rcases Finset.mem_product.mp habt with ⟨ha,hbt⟩
      rcases Finset.mem_product.mp hbt with ⟨hb,ht⟩
      rw [← he]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hg,Finset.mem_product.mpr ⟨ha,ht⟩⟩,
            Finset.mem_product.mpr ⟨hg,Finset.mem_product.mpr ⟨hb,ht⟩⟩⟩
      · change (doublePhase g a t : ℤ) = (doublePhase g b t : ℤ)
        exact_mod_cast hfreq
  rw [heq,Finset.card_image_of_injective _ centerCode_injective]

theorem sum_centers_card_le (h m : Pair) (B : Finset Pair) (Z : Finset ℕ)
    (h₁ : 0 < h.1) (h₂ : 0 < h.2) :
    (∑ n ∈ B, (Z.filter (fun z => doublePhase h m z=doublePhase h n z)).card) ≤
      7*B.card+2*Z.card := by
  classical
  calc
    _ ≤ ∑ n ∈ B, (7 + if doublePolynomial h n=doublePolynomial h m then Z.card else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases he : doublePolynomial h n=doublePolynomial h m
      · rw [if_pos he]
        exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
      · rw [if_neg he,Nat.add_zero]
        exact unequal_polynomial_centers_card_le h m n Z (Ne.symm he)
    _ = 7*B.card+(B.filter (fun n => doublePolynomial h n=doublePolynomial h m)).card*Z.card := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      omega
    _ ≤ 7*B.card+2*Z.card := Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (polynomial_fiber_card_le_two h m B h₁ h₂)) _

/-- The precise diagonal and bounded-root error terms in the odd j=2 step. -/
theorem equalCenterSolutions_card_le (H B : Finset Pair) (Z : Finset ℕ)
    (hH : ∀ h ∈ H, 0 < h.1 ∧ 0 < h.2) :
    (equalCenterSolutions H B Z).card ≤ H.card*B.card*(7*B.card+2*Z.card) := by
  rw [equalCenterSolutions_card]
  calc
    _ ≤ ∑ h ∈ H, ∑ _m ∈ B, (7*B.card+2*Z.card) := by
      apply Finset.sum_le_sum
      intro h hh
      exact Finset.sum_le_sum (fun m hm => sum_centers_card_le h m B Z (hH h hh).1 (hH h hh).2)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]; ring

/-- The entire actual second moment is controlled by the explicit odd-phase
center count, with the divisor factor uniform in all boxes. -/
theorem second_moment {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ H B : Finset Pair, ∀ Z : Finset ℕ,
      (∀ h ∈ H, 0 < h.1 ∧ 0 < h.2) →
      (∀ z ∈ Z, 0 < z) →
      (∀ x ∈ domain H B Z, ((indexPhase x).natAbs : ℝ) ≤ P^L) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ domain H B Z, fourier (indexPhase x) (α : AddCircle (1 : ℝ))‖^2) ≤
          C*P^ε*(H.card : ℝ)*(B.card : ℝ)*(7*(B.card : ℝ)+2*(Z.card : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := frequency_key_multiplicity 3 hL hε
  refine ⟨C,hC,?_⟩
  intro P hP H B Z hH hZ hsize
  let A := domain H B Z
  let K := A.image divisorKey
  have hK : ∀ x ∈ A, divisorKey x ∈ K := fun x hx => Finset.mem_image_of_mem divisorKey hx
  have hne : ∀ x ∈ A, indexPhase x ≠ 0 := by
    intro x hx
    have hh := hH x.1 (Finset.mem_product.mp hx).1
    have hz := hZ x.2.2 (Finset.mem_product.mp (Finset.mem_product.mp hx).2).2
    unfold indexPhase
    exact_mod_cast (doublePhase_pos (m := x.2.1) hh.1 hh.2 hz).ne'
  have hg := secondMoment_le_classes A indexPhase divisorKey K hK
    (D := C*P^ε) (by positivity)
    (hbound P hP Index A indexPhase divisorKey (fun x hx => ⟨hne x hx,hsize x hx⟩)
      (fun x hx i => divisorKey_dvd x i))
  have hc : (∑ k ∈ K, ((collisionPairs (classFiber A divisorKey k) indexPhase).card : ℝ)) =
      ((equalCenterSolutions H B Z).card : ℝ) := by
    rw [← Nat.cast_sum,← sameClassCollisions_card A indexPhase divisorKey K hK]
    exact_mod_cast sameClass_card_eq H B Z
  rw [hc] at hg
  have hb : ((equalCenterSolutions H B Z).card : ℝ) ≤
      (H.card : ℝ)*(B.card : ℝ)*(7*(B.card : ℝ)+2*(Z.card : ℝ)) := by
    exact_mod_cast equalCenterSolutions_card_le H B Z hH
  exact hg.trans (by nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ C*P^ε by positivity)])

#print axioms second_moment
#print axioms equalCenterSolutions_card_le
end Waring.SeedCompletionNinthDoubleCount
