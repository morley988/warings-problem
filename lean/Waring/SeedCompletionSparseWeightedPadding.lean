import Waring.SeedCompletionSparseWeighted

/-! # Extra difference heights with their coefficient fixed at one -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseWeighted

def takeLeft {s t : ℕ} {α : Type*} (x : Fin (s+t) → α) : Fin s → α :=
  fun i => x (Fin.castAdd t i)

def takeRight {s t : ℕ} {α : Type*} (x : Fin (s+t) → α) : Fin t → α :=
  fun i => x (Fin.natAdd s i)

theorem append_take {s t : ℕ} {α : Type*} (x : Fin (s+t) → α) :
    Fin.append (takeLeft x) (takeRight x)=x := Fin.append_castAdd_natAdd

@[simp] theorem takeLeft_append {s t : ℕ} {α : Type*} (a : Fin s → α) (b : Fin t → α) :
    takeLeft (Fin.append a b)=a := by funext i; simp [takeLeft]

@[simp] theorem takeRight_append {s t : ℕ} {α : Type*} (a : Fin s → α) (b : Fin t → α) :
    takeRight (Fin.append a b)=b := by funext i; simp [takeRight]

theorem mem_pi_append {s t : ℕ} (A : Fin s → Finset ℕ) (B : Fin t → Finset ℕ)
    (x : Fin (s+t) → ℕ) :
    x ∈ Fintype.piFinset (Fin.append A B) ↔
      takeLeft x ∈ Fintype.piFinset A ∧ takeRight x ∈ Fintype.piFinset B := by
  simp only [Fintype.mem_piFinset,takeLeft,takeRight]
  constructor
  · intro hx
    exact ⟨fun i => by simpa using hx (Fin.castAdd t i),
      fun i => by simpa using hx (Fin.natAdd s i)⟩
  · rintro ⟨ha,hb⟩ i
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simpa using ha r
    · simpa using hb r

theorem sum_pi_append {s t : ℕ} {R : Type*} [AddCommMonoid R]
    (A : Fin s → Finset ℕ) (B : Fin t → Finset ℕ) (f : (Fin (s+t) → ℕ) → R) :
    (∑ x ∈ Fintype.piFinset (Fin.append A B), f x) =
      ∑ a ∈ Fintype.piFinset A, ∑ b ∈ Fintype.piFinset B, f (Fin.append a b) := by
  classical
  rw [← Finset.sum_product' (Fintype.piFinset A) (Fintype.piFinset B)
    (fun a b => f (Fin.append a b))]
  apply Finset.sum_bij (fun x _ => (takeLeft x,takeRight x))
  · intro x hx
    exact Finset.mem_product.mpr ((mem_pi_append A B x).mp hx)
  · intro x hx y hy he
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    change takeLeft x=takeLeft y at hl
    change takeRight x=takeRight y at hr
    rw [← append_take x,← append_take y,hl,hr]
  · intro ab hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    refine ⟨Fin.append ab.1 ab.2,?_,?_⟩
    · apply (mem_pi_append A B _).mpr
      simpa only [takeLeft_append,takeRight_append] using And.intro ha hb
    · simp only [takeLeft_append,takeRight_append]
  · intro x hx
    rw [append_take]

def appendOnes {s t : ℕ} (m : Fin s → ℕ) : Fin (s+t) → ℕ :=
  Fin.append m (fun _ => 1)

theorem takeRight_eq_one {s t : ℕ} (A : Fin s → Finset ℕ)
    {x : Fin (s+t) → ℕ} (hx : x ∈ Fintype.piFinset (Fin.append A (fun _ => {1}))) :
    takeRight x = fun _ => 1 := by
  funext i
  exact Finset.mem_singleton.mp (Fintype.mem_piFinset.mp (mem_pi_append A _ x |>.mp hx).2 i)

theorem appendOnes_take {s t : ℕ} (A : Fin s → Finset ℕ)
    {x : Fin (s+t) → ℕ} (hx : x ∈ Fintype.piFinset (Fin.append A (fun _ => {1}))) :
    appendOnes (takeLeft x)=x := by
  rw [appendOnes,← takeRight_eq_one A hx,append_take]

theorem vectorFrequency_append {J s t : ℕ} (p q : ℕ) (h : Fin (s+t) → ℕ)
    (m : Fin (s+t) → ℕ) :
    vectorFrequency (fun i => progressionPhase (J := J) p q (h i)) m =
      vectorFrequency (fun i => progressionPhase (J := J) p q (takeLeft h i)) (takeLeft m) +
      vectorFrequency (fun i => progressionPhase (J := J) p q (takeRight h i)) (takeRight m) := by
  funext r
  simp only [vectorFrequency,Finset.sum_apply,Pi.add_apply,Fin.sum_univ_add,takeLeft,takeRight]

theorem vectorCollision_append_ones_card {J s t : ℕ} (p q : ℕ)
    (A : Fin s → Finset ℕ) (h : Fin (s+t) → ℕ) :
    (vectorCollision (Fin.append A (fun _ : Fin t => {1}))
      (fun i => progressionPhase (J := J) p q (h i))).card =
    (vectorCollision A (fun i => progressionPhase (J := J) p q (takeLeft h i))).card := by
  classical
  apply Finset.card_bij (fun xy _ => (takeLeft xy.1,takeLeft xy.2))
  · intro xy hxy
    obtain ⟨hxy,he⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨((mem_pi_append A _ xy.1).mp hx).1,((mem_pi_append A _ xy.2).mp hy).1⟩,?_⟩
    rw [vectorFrequency_append,vectorFrequency_append,takeRight_eq_one A hx,takeRight_eq_one A hy] at he
    exact add_right_cancel he
  · intro xy hxy zw hzw he
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hxy).1
    obtain ⟨hz,hw⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hzw).1
    apply Prod.ext
    · rw [← appendOnes_take A hx,← appendOnes_take A hz]
      exact congrArg appendOnes (congrArg Prod.fst he)
    · rw [← appendOnes_take A hy,← appendOnes_take A hw]
      exact congrArg appendOnes (congrArg Prod.snd he)
  · intro xy hxy
    obtain ⟨hxy,he⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    refine ⟨(appendOnes (t := t) xy.1,appendOnes (t := t) xy.2),?_,?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
      · apply (mem_pi_append A _ _).mpr
        simp only [appendOnes,takeLeft_append,takeRight_append]
        exact ⟨hx,Fintype.mem_piFinset.mpr (fun i => Finset.mem_singleton_self _)⟩
      · apply (mem_pi_append A _ _).mpr
        simp only [appendOnes,takeLeft_append,takeRight_append]
        exact ⟨hy,Fintype.mem_piFinset.mpr (fun i => Finset.mem_singleton_self _)⟩
      · rw [vectorFrequency_append,vectorFrequency_append]
        simpa only [appendOnes,takeLeft_append,takeRight_append] using
          congrArg (fun z => z+vectorFrequency (fun i =>
            progressionPhase (J := J) p q (takeRight h i)) (fun _ => 1)) he
    · simp [appendOnes]

theorem weightedCount_append_ones {J s t : ℕ} (p q : ℕ)
    (H A : Fin s → Finset ℕ) (G : Fin t → Finset ℕ) :
    weightedCount (Fin.append H G) (Fin.append A (fun _ => {1}))
      (fun _ => progressionPhase (J := J) p q) =
    (Fintype.piFinset G).card * weightedCount H A (fun _ => progressionPhase (J := J) p q) := by
  classical
  simp only [weightedCount,vectorCollision_append_ones_card]
  rw [sum_pi_append]
  simp only [takeLeft_append,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,Nat.cast_id]

#print axioms vectorCollision_append_ones_card
#print axioms weightedCount_append_ones
end Waring.SeedCompletionSparseWeighted
