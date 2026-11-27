import Waring.SeedCompletionCurveUniform
import Waring.AuxiliaryL2Grouping

/-! # Uniform collision energy of monotone even polynomial families

A bounded full-polynomial multiplicity supplies the diagonal contribution.
All unequal polynomials use the explicit coefficient-uniform curve count.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionCurveFamilies
open SeedCompletionCurveUniform AuxiliaryL2Grouping

def centerPairs {ι : Type*} (f : ι → ℕ → ℤ) (m n : ι) (Z : Finset ℕ) : Finset (ℕ×ℕ) :=
  (Z ×ˢ Z).filter (fun z => f m z.1=f n z.2)

theorem centerPairs_equal {ι : Type*} (f : ι → ℕ → ℤ) (F : ι → Polynomial ℝ)
    (m n : ι) (Z : Finset ℕ) (hmono : StrictMono (f n))
    (hevalm : ∀ z : ℕ,(F m).eval (z : ℝ)=(f m z : ℝ))
    (hevaln : ∀ z : ℕ,(F n).eval (z : ℝ)=(f n z : ℝ))
    (heq : F m=F n) : (centerPairs f m n Z).card=Z.card := by
  have hfn (z : ℕ) : f m z=f n z := by
    apply (Int.cast_injective (α := ℝ))
    rw [← hevalm,← hevaln,heq]
  have he : centerPairs f m n Z=Z.diag := by
    ext z
    simp only [centerPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_diag,hfn]
    constructor
    · rintro ⟨⟨hz,hw⟩,he⟩
      exact ⟨hz,hmono.injective he⟩
    · rintro ⟨hz,he⟩
      exact ⟨⟨hz,he ▸ hz⟩,congrArg (f n) he⟩
  rw [he,Finset.diag_card]

theorem centerPairs_unequal {ι : Type*} (f : ι → ℕ → ℤ) (F : ι → Polynomial ℝ)
    (m n : ι) (Z : Finset ℕ) (D : ℕ) (hD : 0 < D)
    (hdegm : (F m).natDegree=D) (hdegn : (F n).natDegree=D)
    (hlead : (F m).leadingCoeff=(F n).leadingCoeff)
    (hevenm : ∀ t : ℝ,(F m).eval (-t)=(F m).eval t)
    (hevenn : ∀ t : ℝ,(F n).eval (-t)=(F n).eval t)
    (hmonom : StrictMono (f m)) (hmonon : StrictMono (f n))
    (hevalm : ∀ z : ℕ,(F m).eval (z : ℝ)=(f m z : ℝ))
    (hevaln : ∀ z : ℕ,(F n).eval (z : ℝ)=(f n z : ℝ))
    (hne : F m ≠ F n) (P : ℝ) (hP : 1 ≤ P) (hZ : ∀ z ∈ Z,(z : ℝ) ≤ P) :
    ((centerPairs f m n Z).card : ℝ) ≤ (D : ℝ)*(8*(D : ℝ)^2+3)*P^(2/3 : ℝ) := by
  have hpoints (z : ℕ×ℕ) (hz : z ∈ centerPairs f m n Z) :
      (F m).eval (z.1 : ℝ)=(F n).eval (z.2 : ℝ) := by
    rw [hevalm,hevaln]
    exact_mod_cast (Finset.mem_filter.mp hz).2
  have hinj : Set.InjOn Prod.fst (↑(centerPairs f m n Z) : Set (ℕ×ℕ)) := by
    intro z hz w hw he
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hs : z.2=w.2 := hmonon.injective (by rw [← hz',← hw',he])
    exact Prod.ext he hs
  have horder : ∀ z ∈ centerPairs f m n Z,∀ w ∈ centerPairs f m n Z,
      z.1 < w.1 → z.2 < w.2 := by
    intro z hz w hw he
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have H := hmonom he
    rw [hz',hw'] at H
    exact hmonon.lt_iff_lt.mp H
  have H := separated_even_curve_card_bound (f := F m) (g := F n)
    (by omega) (by omega) hlead hevenm hevenn hne (centerPairs f m n Z) P hP (by
      intro z hz
      have hz' := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
      exact ⟨hZ z.1 hz'.1,hZ z.2 hz'.2⟩) hpoints hinj horder
  simpa only [hdegm] using H

theorem collision_card {ι : Type*} (f : ι → ℕ → ℤ) (B : Finset ι) (Z : Finset ℕ) :
    (collisionPairs (B ×ˢ Z) (fun p => f p.1 p.2)).card =
      ∑ m ∈ B,∑ n ∈ B,(centerPairs f m n Z).card := by
  simp only [collisionPairs,centerPairs,Finset.card_eq_sum_ones,
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]

/-- Exact diagonal multiplicity and uniform unequal-curve contribution. -/
theorem family_collision_card_bound {ι : Type*} (f : ι → ℕ → ℤ)
    (F : ι → Polynomial ℝ) (B : Finset ι) (Z : Finset ℕ) (D K : ℕ) (hD : 0 < D)
    (hdeg : ∀ m ∈ B,(F m).natDegree=D)
    (hlead : ∀ m ∈ B,∀ n ∈ B,(F m).leadingCoeff=(F n).leadingCoeff)
    (heven : ∀ m ∈ B,∀ t : ℝ,(F m).eval (-t)=(F m).eval t)
    (hmono : ∀ m ∈ B,StrictMono (f m))
    (heval : ∀ m ∈ B,∀ z : ℕ,(F m).eval (z : ℝ)=(f m z : ℝ))
    (hfiber : ∀ m ∈ B,(B.filter (fun n => F n=F m)).card ≤ K)
    (P : ℝ) (hP : 1 ≤ P) (hZ : ∀ z ∈ Z,(z : ℝ) ≤ P) :
    ((collisionPairs (B ×ˢ Z) (fun p => f p.1 p.2)).card : ℝ) ≤
      (B.card : ℝ)*((K : ℝ)*(Z.card : ℝ)+
        (B.card : ℝ)*((D : ℝ)*(8*(D : ℝ)^2+3)*P^(2/3 : ℝ))) := by
  classical
  let T : ℝ := (D : ℝ)*(8*(D : ℝ)^2+3)*P^(2/3 : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmBound (m : ι) (hm : m ∈ B) :
      (∑ n ∈ B,((centerPairs f m n Z).card : ℝ)) ≤
        (K : ℝ)*(Z.card : ℝ)+(B.card : ℝ)*T := by
    calc
      _ ≤ ∑ n ∈ B,((if F n=F m then (Z.card : ℝ) else 0)+T) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases he : F n=F m
        · rw [if_pos he,centerPairs_equal f F m n Z (hmono n hn)
            (heval m hm) (heval n hn) he.symm]
          linarith
        · rw [if_neg he,zero_add]
          exact centerPairs_unequal f F m n Z D hD (hdeg m hm) (hdeg n hn)
            (hlead m hm n hn) (heven m hm) (heven n hn) (hmono m hm) (hmono n hn)
            (heval m hm) (heval n hn) (Ne.symm he) P hP hZ
      _ = ((B.filter (fun n => F n=F m)).card : ℝ)*(Z.card : ℝ)+(B.card : ℝ)*T := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter]
        simp
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right
        (by exact_mod_cast hfiber m hm) (Nat.cast_nonneg _)) _
  rw [collision_card,Nat.cast_sum]
  calc
    _ ≤ ∑ _m ∈ B,((K : ℝ)*(Z.card : ℝ)+(B.card : ℝ)*T) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Nat.cast_sum]
      exact hmBound m hm
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T]

#print axioms family_collision_card_bound
end Waring.SeedCompletionCurveFamilies
