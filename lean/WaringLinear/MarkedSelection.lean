import WaringLinear.MarkedChildren

/-! Selection of a group of windows at a common shortening scale. -/
noncomputable section
open Finset
open scoped Classical BigOperators
namespace WaringLinear.MarkedMass

/-- The marked set depends only on its windows, so a selected finite subset
and its complement can be used as the two index types in block deletion. -/
theorem roots_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (P : ℝ) (W : κ → Finset ℕ) :
    roots P (fun i => W (e i)) = roots P W := by
  ext n
  rw [mem_roots,mem_roots]
  constructor
  · rintro ⟨a,y,ha,hy,hmax,he⟩
    have hp := e.symm.prod_comp a
    refine ⟨fun j => a (e.symm j),y,(fun j => by simpa using ha (e.symm j)),hy,?_,?_⟩
    · simpa only [hp] using hmax
    · simpa only [hp] using he
  · rintro ⟨a,y,ha,hy,hmax,he⟩
    have hp := e.prod_comp a
    refine ⟨fun i => a (e i),y,(fun i => ha (e i)),hy,?_,?_⟩
    · simpa only [hp] using hmax
    · simpa only [hp] using he

theorem subset_between {ι : Type*} (S : Finset ι) (v : ι → ℝ) (a δ : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (htotal : a ≤ ∑ i∈S,v i) (hwidth : ∀ i∈S,v i≤δ) :
    ∃ T ⊆ S, a ≤ ∑ i∈T,v i ∧ (∑ i∈T,v i) ≤ a+δ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simpa using htotal,by simp; linarith⟩
  | @insert i S hi ih =>
    by_cases h : a ≤ ∑ j∈S,v j
    · obtain ⟨T,hT,hl,hh⟩ := ih h (fun j hj => hwidth j (mem_insert_of_mem hj))
      exact ⟨T,hT.trans (subset_insert _ _),hl,hh⟩
    · refine ⟨insert i S,Subset.rfl,htotal,?_⟩
      rw [sum_insert hi]
      have hv := hwidth i (mem_insert_self _ _)
      linarith

/-- A single subset of the available primary windows works simultaneously for
every subsequent choice of its primes. Here X=P^x is the current root scale. -/
theorem group_shortening_range {ι : Type*} (P γ x l m δ : ℝ) (v : ι→ℝ) (S : Finset ι)
    (hP : 1 ≤ P) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hl : 0 ≤ l) (hγ : 0 ≤ γ)
    (htotal : x*l ≤ ∑ i∈S,v i) (hwidth : ∀ i∈S, v i ≤ δ)
    (hgap : γ*(x*l+δ) ≤ x*m) :
    ∃ T ⊆ S, ∀ a : ι→ℕ, (∀ i∈T, a i ∈ primeWindow P (v i) γ) →
      (P^x)^l ≤ ((∏ i∈T,a i:ℕ):ℝ) ∧ ((∏ i∈T,a i:ℕ):ℝ) ≤ (P^x)^m := by
  obtain ⟨T,hT,hlo,hhi⟩ := subset_between S v (x*l) δ (mul_nonneg hx hl) hδ htotal hwidth
  refine ⟨T,hT,?_⟩
  intro a ha
  have hP' : 0 < P := zero_lt_one.trans_le hP
  have hmark (i) (hi : i∈T) : P^(v i) ≤ (a i : ℝ) ∧ (a i : ℝ) ≤ P^(γ*v i) := by
    obtain ⟨ht,_⟩ := mem_filter.mp (ha i hi)
    obtain ⟨h1,h2⟩ := mem_Ioc.mp ht
    exact ⟨(Nat.lt_of_floor_lt h1).le,(Nat.le_floor_iff (Real.rpow_nonneg hP'.le _)).mp h2⟩
  rw [Nat.cast_prod, ←Real.rpow_mul hP'.le, ←Real.rpow_mul hP'.le]
  constructor
  · calc
      P^(x*l) ≤ P^(∑ i∈T,v i) := Real.rpow_le_rpow_of_exponent_le hP hlo
      _ = _ := Real.rpow_sum_of_pos hP' v T
      _ ≤ _ := prod_le_prod (fun i _ => Real.rpow_nonneg hP'.le _) (fun i hi => (hmark i hi).1)
  · calc
      (∏ i∈T,(a i : ℝ)) ≤ ∏ i∈T,P^(γ*v i) :=
        prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i hi => (hmark i hi).2)
      _ = P^(γ*∑ i∈T,v i) := by rw [mul_sum,Real.rpow_sum_of_pos hP']
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP ((mul_le_mul_of_nonneg_left hhi hγ).trans hgap)

/-- Every state after deleting primes from the indicated windows has its exact
remaining scale within these two explicit powers of the original root scale. -/
theorem child_scale_bounds {ι : Type*} (P γ : ℝ) (v : ι→ℝ) (S : Finset ι)
    (hP : 1 ≤ P) (a : ι→ℕ) (ha : ∀ i∈S, a i∈primeWindow P (v i) γ) :
    P^(1-γ*∑ i∈S,v i) ≤ P/((∏ i∈S,a i:ℕ):ℝ) ∧
      P/((∏ i∈S,a i:ℕ):ℝ) ≤ P^(1-∑ i∈S,v i) := by
  have hP' := zero_lt_one.trans_le hP
  have hmark (i) (hi : i∈S) : P^(v i) ≤ (a i : ℝ) ∧ (a i : ℝ) ≤ P^(γ*v i) := by
    obtain ⟨ht,_⟩ := mem_filter.mp (ha i hi)
    obtain ⟨h1,h2⟩ := mem_Ioc.mp ht
    exact ⟨(Nat.lt_of_floor_lt h1).le,(Nat.le_floor_iff (Real.rpow_nonneg hP'.le _)).mp h2⟩
  have hd : 0 < (∏ i∈S,(a i : ℝ)) := prod_pos (fun i hi =>
    (Real.rpow_pos_of_pos hP' _).trans_le (hmark i hi).1)
  rw [Nat.cast_prod, Real.rpow_sub hP', Real.rpow_sub hP',Real.rpow_one]
  constructor
  · apply div_le_div_of_nonneg_left hP'.le hd
    rw [mul_sum, Real.rpow_sum_of_pos hP']
    exact prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i hi => (hmark i hi).2)
  · apply div_le_div_of_nonneg_left hP'.le (Real.rpow_pos_of_pos hP' _)
    rw [Real.rpow_sum_of_pos hP']
    exact prod_le_prod (fun i _ => Real.rpow_nonneg hP'.le _) (fun i hi => (hmark i hi).1)

#print axioms group_shortening_range
#print axioms child_scale_bounds

/-- All prime factors in a shortened state lie below the prescribed smooth cutoff
on its own scale. The lower bound P^δ for that scale follows solely from the
removed-window exponent budget. -/
theorem child_smooth_at_scale (P γ δ η : ℝ) {α β : Type*} [Fintype α] [Fintype β]
    (u : α → ℝ) (v : β → ℝ) (a : α→ℕ)
    (hP : 1 < P) (hη : 0 ≤ η)
    (ha : ∀ i, a i ∈ primeWindow P (u i) γ)
    (hscale : δ ≤ 1 - γ*(∑ i,u i))
    (hmarks : ∀ j, γ*v j ≤ δ*η)
    (hcof : 1 - (∑ i,u i) - (∑ j,v j) ≤ δ*η) :
    let X := P/((∏ i,a i:ℕ):ℝ)
    roots X (fun j=>primeWindow P (v j) γ) ⊆ Waring.SmoothMoments.smoothNumbers X (X^η) := by
  intro X
  have hP' := zero_lt_one.trans hP
  have hs := child_scale_bounds P γ u univ hP.le a (fun i _ => ha i)
  have hX : P^δ ≤ X := (Real.rpow_le_rpow_of_exponent_le hP.le hscale).trans hs.1
  have hXη : P^(δ*η) ≤ X^η := by
    rw [Real.rpow_mul hP'.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hP'.le _) hX hη
  apply roots_subset_smooth
  · exact fun j p hp => (mem_filter.mp hp).2
  · intro j p hp
    obtain ⟨hj,_⟩ := mem_filter.mp hp
    have hp' := (Nat.le_floor_iff (Real.rpow_nonneg hP'.le _)).mp (mem_Ioc.mp hj).2
    exact hp'.trans ((Real.rpow_le_rpow_of_exponent_le hP.le (hmarks j)).trans hXη)
  · intro b hb
    have hd : P^(∑ j,v j) ≤ ((∏ j,b j:ℕ):ℝ) := by
      rw [Nat.cast_prod,Real.rpow_sum_of_pos hP']
      apply prod_le_prod (fun j _ => Real.rpow_nonneg hP'.le _)
      intro j _
      obtain ⟨hj,_⟩ := mem_filter.mp (Fintype.mem_piFinset.mp hb j)
      exact (Nat.lt_of_floor_lt (mem_Ioc.mp hj).1).le
    have hdp := (Real.rpow_pos_of_pos hP' _).trans_le hd
    calc
      X/_ ≤ P^(1-∑ i,u i)/P^(∑ j,v j) :=
        (div_le_div_of_nonneg_right hs.2 hdp.le).trans
          (div_le_div_of_nonneg_left (Real.rpow_nonneg hP'.le _) (Real.rpow_pos_of_pos hP' _) hd)
      _ = P^(1-(∑ i,u i)-(∑ j,v j)) := (Real.rpow_sub hP' _ _).symm
      _ ≤ _ := (Real.rpow_le_rpow_of_exponent_le hP.le hcof).trans hXη

#print axioms child_smooth_at_scale

end WaringLinear.MarkedMass

