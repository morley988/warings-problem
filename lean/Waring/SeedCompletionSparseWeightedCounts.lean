import Waring.SeedCompletionSparseWeightedEncoding

/-! # Exact Fourier identities for heterogeneous vector collision counts -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseWeighted
open PolicyCompletionHolder AuxiliaryL2Grouping

def vectorFrequency {J s : ℕ} (v : Fin s → ℕ → Fin J → ℤ)
    (m : Fin s → ℕ) : Fin J → ℤ := ∑ i, v i (m i)

def vectorCollision {J s : ℕ} (A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → Fin J → ℤ) :=
  ((Fintype.piFinset A) ×ˢ (Fintype.piFinset A)).filter
    (fun xy => vectorFrequency v xy.1 = vectorFrequency v xy.2)

def constraintVectors {J s : ℕ} (A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → Fin J → ℤ) : Finset (Fin J → ℤ) :=
  ((Fintype.piFinset A) ×ˢ (Fintype.piFinset A)).image
    (fun xy => vectorFrequency v xy.1 - vectorFrequency v xy.2)

theorem frequencySum_pi {s : ℕ} (A : Fin s → Finset ℕ)
    (f : Fin s → ℕ → ℤ) (x : ℝ) :
    frequencySum (Fintype.piFinset A) (fun m => ∑ i, f i (m i)) x =
      ∏ i, frequencySum (A i) (f i) x := by
  classical
  unfold frequencySum
  rw [Finset.prod_univ_sum]
  simp_rw [prod_fourier_character]

theorem vectorCollision_eq_integral {J s : ℕ} (A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → Fin J → ℤ) (b : ℤ)
    (hb : ∀ d ∈ constraintVectors A v, code b d=0 ↔ d=0) :
    ((vectorCollision A v).card : ℝ) =
      ∫ x in (0 : ℝ)..1, ∏ i, ‖frequencySum (A i) (fun m => code b (v i m)) x‖^2 := by
  classical
  have hcode (m : Fin s → ℕ) :
      code b (vectorFrequency v m) = ∑ i, code b (v i (m i)) :=
    code_sum b Finset.univ (fun i => v i (m i))
  have he : vectorCollision A v =
      collisionPairs (Fintype.piFinset A) (fun m => ∑ i, code b (v i (m i))) := by
    apply Finset.filter_congr
    intro xy hxy
    change (vectorFrequency v xy.1 = vectorFrequency v xy.2) ↔
      ((∑ i, code b (v i (xy.1 i))) = ∑ i, code b (v i (xy.2 i)))
    rw [← hcode, ← hcode]
    have hh := hb _ (Finset.mem_image.mpr ⟨xy,hxy,rfl⟩)
    rw [code_sub] at hh
    simpa only [sub_eq_zero] using hh.symm
  rw [he]
  have hpoint (x : ℝ) :
      ‖frequencySum (Fintype.piFinset A) (fun m => ∑ i, code b (v i (m i))) x‖^2 =
        ∏ i, ‖frequencySum (A i) (fun m => code b (v i m)) x‖^2 := by
    rw [frequencySum_pi A (fun i m => code b (v i m)) x,norm_prod,Finset.prod_pow]
  calc
    _ = ∫ x in (0 : ℝ)..1,
        ‖frequencySum (Fintype.piFinset A) (fun m => ∑ i, code b (v i (m i))) x‖^2 :=
      (interval_integral_sq_norm_eq_collision_count (Fintype.piFinset A)
        (fun m => ∑ i, code b (v i (m i)))).symm
    _ = _ := intervalIntegral.integral_congr (fun x _ => hpoint x)

def allConstraintVectors {J s : ℕ} (H A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → ℕ → Fin J → ℤ) : Finset (Fin J → ℤ) :=
  ((Fintype.piFinset H).biUnion (fun h => constraintVectors A (fun i => v i (h i)))) ∪
  Finset.univ.biUnion (fun i => (H i).biUnion (fun h =>
    constraintVectors (fun _ : Fin s => A i) (fun _ => v i h)))

theorem exists_joint_code {J s : ℕ} (H A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → ℕ → Fin J → ℤ) :
    ∃ b : ℤ,
      (∀ h ∈ Fintype.piFinset H, ∀ d ∈ constraintVectors A (fun i => v i (h i)),
        code b d=0 ↔ d=0) ∧
      (∀ i, ∀ h ∈ H i, ∀ d ∈ constraintVectors (fun _ : Fin s => A i) (fun _ => v i h),
        code b d=0 ↔ d=0) := by
  classical
  obtain ⟨b,hb⟩ := exists_code_detecting_zero (allConstraintVectors H A v)
  refine ⟨b,?_,?_⟩
  · intro h hh d hd
    exact hb d (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨h,hh,hd⟩))
  · intro i h hh d hd
    exact hb d (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨h,hh,hd⟩⟩))

def heightSum {J s : ℕ} (H A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → ℕ → Fin J → ℤ) (b : ℤ) (i : Fin s) (x : ℝ) : ℝ :=
  ∑ h ∈ H i, ‖frequencySum (A i) (fun m => code b (v i h m)) x‖^2

def weightedCount {J s : ℕ} (H A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → ℕ → Fin J → ℤ) : ℕ :=
  ∑ h ∈ Fintype.piFinset H, (vectorCollision A (fun i => v i (h i))).card

theorem continuous_heightSum {J s : ℕ} (H A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → ℕ → Fin J → ℤ) (b : ℤ) (i : Fin s) :
    Continuous (heightSum H A v b i) :=
  continuous_finset_sum _ (fun h _ => (continuous_frequencySum _ _).norm.pow 2)

theorem heightSum_nonneg {J s : ℕ} (H A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → ℕ → Fin J → ℤ) (b : ℤ) (i : Fin s) (x : ℝ) :
    0 ≤ heightSum H A v b i x := by
  unfold heightSum
  positivity

theorem weightedCount_eq_integral {J s : ℕ} (H A : Fin s → Finset ℕ)
    (v : Fin s → ℕ → ℕ → Fin J → ℤ) (b : ℤ)
    (hb : ∀ h ∈ Fintype.piFinset H, ∀ d ∈ constraintVectors A (fun i => v i (h i)),
      code b d=0 ↔ d=0) :
    (weightedCount H A v : ℝ) = ∫ x in (0 : ℝ)..1, ∏ i, heightSum H A v b i x := by
  classical
  unfold weightedCount
  rw [Nat.cast_sum]
  simp_rw [heightSum,Finset.prod_univ_sum]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro h hh
    exact vectorCollision_eq_integral A (fun i => v i (h i)) b (hb h hh)
  · intro h hh
    exact (continuous_finset_prod Finset.univ (fun i _ =>
      (continuous_frequencySum _ _).norm.pow 2)).intervalIntegrable 0 1

#print axioms vectorCollision_eq_integral
#print axioms weightedCount_eq_integral
end Waring.SeedCompletionSparseWeighted
