import WaringSiegel.WSL4MixedOffdiagonal
import WaringSiegel.WSL4MixedSixthFourier

/-! # Exact separation of the diagonal in the congruent mixed count -/
noncomputable section
set_option maxHeartbeats 1500000
open NumberField
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {K : Type*} [Field K] [NumberField K]

def cubicFourthBoxPhase (Y : Finset (𝓞 K)) (y : (Y × Y) × (Y × Y)) : 𝓞 K :=
  (y.1.1.val^3-y.1.2.val^3)+(y.2.1.val^3-y.2.2.val^3)

def cubicFourthBoxCount (Y : Finset (𝓞 K)) : ℕ :=
  Fintype.card {y : (Y × Y) × (Y × Y) // cubicFourthBoxPhase Y y=0}

theorem card_subtype_eq_sum_indicator {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    Fintype.card {a // p a} = ∑ a, if p a then 1 else 0 := by
  rw [Fintype.card_subtype,← Finset.sum_filter]
  simp

theorem congruent_mixed_count_diagonal_split (X M Y : Finset (𝓞 K))
    (hM : ∀ m ∈ M, m ≠ 0) :
    (∑ m : M, mixedResidueCongruentCount (m.val^3)
      (fun x : X => (x : 𝓞 K)) (fun y : Y => (y : 𝓞 K))) =
      M.card*X.card*cubicFourthBoxCount Y + mixedCongruentOffdiagonalCount X M Y := by
  let A := (X × X) × ((Y × Y) × (Y × Y))
  have hres (m : M) (t : A) :
      Ideal.Quotient.mk (Ideal.span ({m.val^3} : Set (𝓞 K))) t.1.1.val =
        Ideal.Quotient.mk (Ideal.span ({m.val^3} : Set (𝓞 K))) t.1.2.val ↔
      m.val^3 ∣ t.1.2.val-t.1.1.val := by
    rw [← sub_eq_zero,← map_sub,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
    exact dvd_sub_comm
  have hsplit (m : M) (t : A) :
      (if m.val^3 ∣ t.1.2.val-t.1.1.val ∧
        mixedSecondFourthPhase (m.val^3) (fun x : X => x.val) (fun y : Y => y.val) t=0 then 1 else 0) =
      (if t.1.1=t.1.2 ∧ cubicFourthBoxPhase Y t.2=0 then 1 else 0) +
      (if t.1.1.val≠t.1.2.val ∧ m.val^3 ∣ t.1.2.val-t.1.1.val ∧
        mixedCubicBoxPhase X M Y (m,t)=0 then 1 else 0) := by
    by_cases hxy : t.1.1=t.1.2
    · have hp : mixedSecondFourthPhase (m.val^3) (fun x : X => x.val) (fun y : Y => y.val) t=0 ↔
        cubicFourthBoxPhase Y t.2=0 := by
        simp only [mixedSecondFourthPhase,hxy,sub_self,zero_add,cubicFourthBoxPhase,
          mul_eq_zero,pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0),hM m.val m.property,false_or]
      simp only [hxy,sub_self,dvd_zero,true_and,hp,ne_eq,not_true_eq_false,
        false_and,if_false,add_zero]
    · have hval : t.1.1.val≠t.1.2.val := fun h => hxy (Subtype.ext h)
      simp [hxy,hval,mixedSecondFourthPhase,mixedCubicBoxPhase]
  have hdiag : (∑ t : A, if t.1.1=t.1.2 ∧ cubicFourthBoxPhase Y t.2=0 then 1 else 0) =
      X.card*cubicFourthBoxCount Y := by
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    have hh (x₁ x₂ : X) (y : (Y × Y) × (Y × Y)) :
        (if x₁=x₂ ∧ cubicFourthBoxPhase Y y=0 then (1 : ℕ) else 0) =
        if x₁=x₂ then (if cubicFourthBoxPhase Y y=0 then 1 else 0) else 0 := by
      split_ifs <;> simp_all
    simp_rw [hh,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp [cubicFourthBoxCount,card_subtype_eq_sum_indicator]
  have hcount (m:M) : mixedResidueCongruentCount (m.val^3)
      (fun x:X => x.val) (fun y:Y => y.val) =
      ∑ t:A, if Ideal.Quotient.mk (Ideal.span ({m.val^3}:Set (𝓞 K))) t.1.1.val =
        Ideal.Quotient.mk (Ideal.span ({m.val^3}:Set (𝓞 K))) t.1.2.val ∧
        mixedSecondFourthPhase (m.val^3) (fun x:X=>x.val) (fun y:Y=>y.val) t=0
        then 1 else 0 := by
    simpa only [mixedResidueCongruentCount,A] using
      (card_subtype_eq_sum_indicator (A:=A) (fun t =>
        Ideal.Quotient.mk (Ideal.span ({m.val^3}:Set (𝓞 K))) t.1.1.val =
          Ideal.Quotient.mk (Ideal.span ({m.val^3}:Set (𝓞 K))) t.1.2.val ∧
        mixedSecondFourthPhase (m.val^3) (fun x:X=>x.val) (fun y:Y=>y.val) t=0))
  simp_rw [hcount,hres,hsplit,Finset.sum_add_distrib,hdiag]
  have hoff : (∑ m : M, ∑ t : A,
      if t.1.1.val≠t.1.2.val ∧ m.val^3 ∣ t.1.2.val-t.1.1.val ∧
        mixedCubicBoxPhase X M Y (m,t)=0 then 1 else 0) =
      mixedCongruentOffdiagonalCount X M Y := by
    change _ = Fintype.card {t:M×A // t.2.1.1.val≠t.2.1.2.val ∧
      t.1.val^3∣t.2.1.2.val-t.2.1.1.val ∧ mixedCubicBoxPhase X M Y t=0}
    have he := card_subtype_eq_sum_indicator (A:=M×A) (fun t =>
      t.2.1.1.val≠t.2.1.2.val ∧ t.1.val^3∣t.2.1.2.val-t.2.1.1.val ∧
        mixedCubicBoxPhase X M Y t=0)
    rw [Fintype.sum_prod_type] at he
    exact he.symm
  rw [hoff]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  norm_cast
  ac_rfl

#print axioms congruent_mixed_count_diagonal_split
end WaringSiegel.WSL4Local
