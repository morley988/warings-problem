import Waring.EndgameCompletionMinorTransfer
import Waring.EndgameCompletionOrdinary

/-!
# Strong full ordinary and smooth moments

The proved broad-major and minor estimates give the exact no-epsilon
90th moments. Smooth even moments follow from literal solution-set
inclusion, and higher moments follow from the trivial pointwise bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Waring.EndgameCompletion
open MixedEndgame SmoothMoments

theorem degree8_ordinary90_strong :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ordinaryMoment 8 90 N≤C*(N : ℝ)^82 := by
  obtain ⟨A,hA,hmajor⟩ := degree8_ordinary_broad_major12
  obtain ⟨B,hB,hminor⟩ := degree8_ordinary_minor72 (ε := 1) (by norm_num)
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro N hN
  exact ordinary90_of_major12_minor72 (by exact_mod_cast hN) hA.le hB.le le_rfl
    (ordinary_major_minor_cover 8 N) (hmajor N (by exact_mod_cast hN)) (hminor N hN)

theorem degree9_ordinary90_strong :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ordinaryMoment 9 90 N≤C*(N : ℝ)^81 := by
  obtain ⟨A,hA,hmajor⟩ := degree9_ordinary_broad_major11
  obtain ⟨B,hB,hminor⟩ := degree9_ordinary_minor90 (ε := 1) (by norm_num)
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro N hN
  have hn : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hM : ordinaryArcMoment 9 90 N (ordinaryBroadMajor 9 N)≤
      ENNReal.ofReal (A*(N : ℝ)^81) := by
    calc
      _ ≤ ENNReal.ofReal ((N : ℝ)^79)*ordinaryArcMoment 9 11 N (ordinaryBroadMajor 9 N) :=
        ordinaryArcMoment_order_growth 9 11 90 _ (by norm_num) hn
      _ ≤ ENNReal.ofReal ((N : ℝ)^79)*ENNReal.ofReal (A*(N : ℝ)^2) :=
        mul_le_mul_left' (hmajor N (by exact_mod_cast hN)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hm : ordinaryArcMoment 9 90 N (ordinaryMinorRegion 9 N)≤
      ENNReal.ofReal (B*(N : ℝ)^81) := by
    simpa only [show (80 : ℝ)+1=((81 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] using hminor N hN
  have hh : ENNReal.ofReal (ordinaryMoment 9 90 N)≤ENNReal.ofReal ((A+B)*(N : ℝ)^81) := by
    rw [← ordinaryArcMoment_full,← ordinary_major_minor_cover 9 N]
    calc
      _ ≤ ordinaryArcMoment 9 90 N (ordinaryBroadMajor 9 N)+
          ordinaryArcMoment 9 90 N (ordinaryMinorRegion 9 N) := lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (A*(N : ℝ)^81)+ENNReal.ofReal (B*(N : ℝ)^81) := add_le_add hM hm
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

/-- The no-epsilon smooth degree-eight 90th moment is unconditional. -/
theorem degree8_smooth90_strong :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ∀ R : ℝ,
      smoothMoment 8 90 N R≤C*(N : ℝ)^82 := by
  obtain ⟨C,hC,hbound⟩ := degree8_ordinary90_strong
  exact ⟨C,hC,fun N hN R=>(smoothMoment_even_le_ordinaryMoment 8 45 N R).trans (hbound N hN)⟩

theorem degree9_smooth90_strong :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ∀ R : ℝ,
      smoothMoment 9 90 N R≤C*(N : ℝ)^81 := by
  obtain ⟨C,hC,hbound⟩ := degree9_ordinary90_strong
  exact ⟨C,hC,fun N hN R=>(smoothMoment_even_le_ordinaryMoment 9 45 N R).trans (hbound N hN)⟩

theorem ordinaryMoment_order_growth (k p q : ℕ) {P : ℝ} (hP : 0≤P) (hpq : p≤q) :
    ordinaryMoment k q P≤P^(q-p)*ordinaryMoment k p P := by
  have hh := ordinaryArcMoment_order_growth k p q (Set.Ioc 0 1) hpq hP
  rw [ordinaryArcMoment_full,ordinaryArcMoment_full,
    ← ENNReal.ofReal_mul (by positivity)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (pow_nonneg hP _) (ordinaryMoment_nonneg k p P))).mp hh

/-- A spare high even moment for alternative degree-nine pruning
allocations, obtained solely by growth and finite-count inclusion. -/
theorem degree9_smooth420_strong :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ∀ R : ℝ,
      smoothMoment 9 420 N R≤C*(N : ℝ)^411 := by
  obtain ⟨C,hC,hbound⟩ := degree9_ordinary90_strong
  refine ⟨C,hC,?_⟩
  intro N hN R
  calc
    _ ≤ ordinaryMoment 9 420 N := smoothMoment_even_le_ordinaryMoment 9 210 N R
    _ ≤ (N : ℝ)^330*ordinaryMoment 9 90 N :=
      ordinaryMoment_order_growth 9 90 420 (Nat.cast_nonneg _) (by norm_num)
    _ ≤ (N : ℝ)^330*(C*(N : ℝ)^81) :=
      mul_le_mul_of_nonneg_left (hbound N hN) (by positivity)
    _ = _ := by ring

#print axioms degree8_ordinary90_strong
#print axioms degree9_ordinary90_strong
#print axioms degree8_smooth90_strong
#print axioms degree9_smooth420_strong
end Waring.EndgameCompletion
