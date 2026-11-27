import Waring.SeedCompletionCurveParityUniform
import Waring.SeedCompletionCurveFamilies

/-! # Uniform collision energy for polynomial families of common parity -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionCurveParityFamilies
open SeedCompletionCurveParityUniform SeedCompletionCurveFamilies AuxiliaryL2Grouping

theorem centerPairs_unequal_parity {ι : Type*} {σ : ℝ} (f : ι → ℕ → ℤ) (F : ι → Polynomial ℝ)
    (m n : ι) (Z : Finset ℕ) (D : ℕ) (hD : 0 < D)
    (hdegm : (F m).natDegree=D) (hdegn : (F n).natDegree=D)
    (hlead : (F m).leadingCoeff=(F n).leadingCoeff)
    (hσ : σ^2=1) (hparm : ∀ t : ℝ,(F m).eval (-t)=σ*(F m).eval t)
    (hparn : ∀ t : ℝ,(F n).eval (-t)=σ*(F n).eval t)
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
  have H := separated_parity_curve_card_bound (f := F m) (g := F n)
    (by omega) (by omega) hlead hσ hparm hparn hne (centerPairs f m n Z) P hP (by
      intro z hz
      have hz' := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
      exact ⟨hZ z.1 hz'.1,hZ z.2 hz'.2⟩) hpoints hinj horder
  simpa only [hdegm] using H

/-- Exact diagonal multiplicity and uniform unequal-curve contribution. -/
theorem family_collision_card_bound_parity {ι : Type*} {σ : ℝ} (f : ι → ℕ → ℤ)
    (F : ι → Polynomial ℝ) (B : Finset ι) (Z : Finset ℕ) (D K : ℕ) (hD : 0 < D)
    (hdeg : ∀ m ∈ B,(F m).natDegree=D)
    (hlead : ∀ m ∈ B,∀ n ∈ B,(F m).leadingCoeff=(F n).leadingCoeff)
    (hσ : σ^2=1) (hpar : ∀ m ∈ B,∀ t : ℝ,(F m).eval (-t)=σ*(F m).eval t)
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
          exact centerPairs_unequal_parity f F m n Z D hD (hdeg m hm) (hdeg n hn)
            (hlead m hm n hn) hσ (hpar m hm) (hpar n hn) (hmono m hm) (hmono n hn)
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

#print axioms family_collision_card_bound_parity
end Waring.SeedCompletionCurveParityFamilies
