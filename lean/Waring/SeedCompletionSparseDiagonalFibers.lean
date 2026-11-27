import Waring.SeedCompletionSparseDiagonalNewton
import Waring.DifferenceSquaresFibers
import Waring.AuxiliaryL2Grouping

/-! # Exact sparse diagonal fibers and their divisor injection -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseDiagonal
open FiniteFieldMordell DifferenceSquaresFibers

/-- The natural variables are raised first to the fixed progression step. -/
def sparseSignedMoment {J : ℕ} (p : ℕ) (x : Fin (J+1) → ℕ) (r : ℕ) : ℤ :=
  (∑i : Fin J,(x i.succ : ℤ)^(p*r))-(x 0 : ℤ)^(p*r)

def differenceKey {J : ℕ} (p : ℕ) (x : Fin (J+1) → ℕ) : Fin J → ℤ :=
  fun i => (x 0 : ℤ)^p-(x i.succ : ℤ)^p

def differenceProduct {J : ℕ} (p : ℕ) (x : Fin (J+1) → ℕ) : ℤ :=
  ∏i,differenceKey p x i

theorem differenceProduct_eq {J p : ℕ} {x y : Fin (J+1) → ℕ}
    (hs : ∀ r : ℕ, 1 ≤ r → r ≤ J → sparseSignedMoment p x r=sparseSignedMoment p y r) :
    differenceProduct p x=differenceProduct p y := by
  have hq : ∀ r : ℕ, 1 ≤ r → r ≤ J →
      signedPower (fun i => (x i : ℚ)^p) r=signedPower (fun i => (y i : ℚ)^p) r := by
    intro r hr hrJ
    have hh := hs r hr hrJ
    unfold sparseSignedMoment at hh
    unfold signedPower
    simp only [← pow_mul]
    exact_mod_cast hh
  have he := signedProduct_eq_rat hq
  unfold signedProduct at he
  apply (Int.cast_injective (α := ℚ))
  simpa only [differenceProduct,differenceKey,Int.cast_prod,Int.cast_sub,Int.cast_pow,Int.cast_natCast] using he

theorem differenceKey_inj_of_first_moment {J p : ℕ} (hJ : 2 ≤ J) (hp : 0 < p)
    {x y : Fin (J+1) → ℕ}
    (hs : sparseSignedMoment p x 1=sparseSignedMoment p y 1)
    (hd : differenceKey p x=differenceKey p y) : x=y := by
  have hsum := congrArg (fun z : Fin J → ℤ => ∑i,z i) hd
  simp only [differenceKey,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  simp only [sparseSignedMoment,Nat.mul_one] at hs
  have hcenter : ((J : ℤ)-1)*(x 0 : ℤ)^p=((J : ℤ)-1)*(y 0 : ℤ)^p := by
    linear_combination hsum+hs
  have hJne : (J : ℤ)-1 ≠ 0 := by omega
  have hc : x 0=y 0 := Nat.pow_left_injective hp.ne' (by
    exact_mod_cast mul_left_cancel₀ hJne hcenter)
  ext i
  refine Fin.cases hc (fun j => ?_) i
  have hh := congrFun hd j
  simp only [differenceKey,hc] at hh
  apply Nat.pow_left_injective hp.ne'
  exact_mod_cast sub_right_injective hh

/-- A finite family with all first s progression power sums equal has at
most s^s members. The bound deliberately keeps a simple fixed constant. -/
theorem power_family_card_le {s p : ℕ} (hp : 0 < p) (S : Finset (Fin s → ℕ))
    (hs : ∀x∈S,∀y∈S,∀ r : ℕ, 1 ≤ r → r ≤ s →
      (∑i,(x i : ℤ)^(p*r))=∑i,(y i : ℤ)^(p*r)) : S.card ≤ s^s := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨x,hx⟩ := hS
    have hsub : S ⊆ finiteTuples (Finset.univ.image x) s := by
      intro y hy
      apply Fintype.mem_piFinset.mpr
      intro j
      have hpowers : ∀ r : ℕ, 1 ≤ r → r ≤ s →
          (∑i,((x i : ℚ)^p)^r)=∑i,((y i : ℚ)^p)^r := by
        intro r hr hrs
        simp only [← pow_mul]
        exact_mod_cast hs x hx y hy r hr hrs
      obtain ⟨i,hi⟩ := coordinate_mem_of_power_sums
        (fun r hr _ => by exact_mod_cast (show r≠0 by omega)) hpowers j
      have hij : x i=y j := Nat.pow_left_injective hp.ne' (by exact_mod_cast hi)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hij⟩
    calc
      _ ≤ (finiteTuples (Finset.univ.image x) s).card := Finset.card_le_card hsub
      _ = (Finset.univ.image x).card^s := by simp [finiteTuples,Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by simpa using Finset.card_image_le (s := Finset.univ) (f := x)) s
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty]
    exact Nat.zero_le _

theorem nonzero_signed_fiber_card_le {J p : ℕ} (hJ : 2 ≤ J) (hp : 0 < p)
    (S : Finset (Fin (J+1) → ℕ)) (y : Fin (J+1) → ℕ)
    (hy : differenceProduct p y ≠ 0)
    (hs : ∀x∈S,∀ r : ℕ, 1 ≤ r → r ≤ J →
      sparseSignedMoment p x r=sparseSignedMoment p y r) :
    S.card ≤ (2*(differenceProduct p y).natAbs.divisors.card)^J := by
  classical
  have hc : S.card ≤ (finiteTuples (signedDivisors (differenceProduct p y)) J).card := by
    apply Finset.card_le_card_of_injOn (differenceKey p)
    · intro x hx
      apply Fintype.mem_piFinset.mpr
      intro i
      apply mem_signedDivisors hy
      rw [← differenceProduct_eq (hs x hx)]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    · intro x hx z hz hkey
      exact differenceKey_inj_of_first_moment hJ hp
        ((hs x hx 1 (by omega) (by omega)).trans (hs z hz 1 (by omega) (by omega)).symm) hkey
  calc
    _ ≤ _ := hc
    _ = (signedDivisors (differenceProduct p y)).card^J := by
      simp [finiteTuples,Fintype.card_piFinset]
    _ ≤ _ := Nat.pow_le_pow_left (card_signedDivisors_le _) J

#print axioms differenceProduct_eq
#print axioms power_family_card_le
#print axioms nonzero_signed_fiber_card_le
end Waring.SeedCompletionSparseDiagonal
