import WaringSiegel.WSL4WeilVandermondeValuation
import WaringSiegel.WSL4RamanujamQBinomial

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1000000

private theorem prod_fin_erase_eq_range_erase
    {R : Type*} [CommMonoid R] (n : ℕ) (j : Fin (n+1)) (f : ℕ → R) :
    (∏ i∈Finset.univ.erase j,f i.val)=∏ i∈(Finset.range (n+1)).erase j.val,f i := by
  refine Finset.prod_nbij Fin.val ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    exact Finset.mem_erase.mpr ⟨(fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)),
      Finset.mem_range.mpr i.isLt⟩
  · exact Fin.val_injective.injOn
  · intro i hi
    have hir := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    refine ⟨⟨i,hir⟩,?_,rfl⟩
    exact Finset.mem_erase.mpr ⟨(fun h => (Finset.mem_erase.mp hi).1 (congrArg Fin.val h)),
      Finset.mem_univ _⟩

theorem geometric_denominator_factor
    {R : Type*} [CommRing R] (y : R) (n : ℕ) (j : Fin (n+1)) :
    (∏ i∈Finset.univ.erase j,(y^j.val-y^i.val))=
      (-1)^j.val*y^(j.val*(j.val-1)/2+(n-j.val)*j.val)*
        (∏ i∈Finset.range j.val,(1-y^(i+1)))*
        (∏ i∈Finset.range (n-j.val),(1-y^(i+1))) := by
  have hpart : (Finset.range (n+1)).erase j.val=
      Finset.range j.val ∪ Finset.Ico (j.val+1) (n+1) := by
    ext i
    simp only [Finset.mem_erase,Finset.mem_range,Finset.mem_union,Finset.mem_Ico]
    omega
  have hdis : Disjoint (Finset.range j.val) (Finset.Ico (j.val+1) (n+1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have := Finset.mem_range.mp hi
    have := (Finset.mem_Ico.mp hi').1
    omega
  have hrev : (∏ i∈Finset.range j.val,(1-y^(j.val-i)))=
      ∏ i∈Finset.range j.val,(1-y^(i+1)) := by
    calc
      _ = ∏ i∈Finset.range j.val,(1-y^(j.val-1-i+1)) := by
        apply Finset.prod_congr rfl
        intro i hi
        congr 2
        have := Finset.mem_range.mp hi
        omega
      _ = _ := Finset.prod_range_reflect (fun i => 1-y^(i+1)) j.val
  have hlo : (∏ i∈Finset.range j.val,(y^j.val-y^i))=
      (-1)^j.val*y^(j.val*(j.val-1)/2)*(∏ i∈Finset.range j.val,(1-y^(i+1))) := by
    calc
      _ = ∏ i∈Finset.range j.val,((-1)*y^i)*(1-y^(j.val-i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        have he : j.val=i+(j.val-i) := by have := Finset.mem_range.mp hi; omega
        conv_lhs => rw [he,pow_add]
        ring
      _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,
          Finset.prod_const,Finset.card_range,Finset.prod_pow_eq_pow_sum,
          Finset.sum_range_id,hrev]
  have hhi : (∏ i∈Finset.Ico (j.val+1) (n+1),(y^j.val-y^i))=
      y^((n-j.val)*j.val)*(∏ i∈Finset.range (n-j.val),(1-y^(i+1))) := by
    rw [Finset.prod_Ico_eq_prod_range]
    have hlen : n+1-(j.val+1)=n-j.val := by omega
    rw [hlen]
    calc
      _ = ∏ i∈Finset.range (n-j.val),y^j.val*(1-y^(i+1)) := by
        apply Finset.prod_congr rfl
        intro i hi
        have he : j.val+1+i=j.val+(i+1) := by omega
        rw [he,pow_add]
        ring
      _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,← pow_mul]
        rw [Nat.mul_comm j.val (n-j.val)]
  rw [prod_fin_erase_eq_range_erase n j (fun i : ℕ => y^j.val-y^i),hpart,Finset.prod_union hdis,hlo,hhi,pow_add]
  ring

theorem geometric_denominator_polynomial_factor (n : ℕ) (j : Fin (n+1)) :
    (∏ i∈Finset.univ.erase j,((X:ℤ[X])^j.val-X^i.val))=
      (-1)^j.val*X^(j.val*(j.val-1)/2+(n-j.val)*j.val)*
        WSL4Local.qFactorial j.val*WSL4Local.qFactorial (n-j.val) := by
  exact geometric_denominator_factor X n j
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.geometric_denominator_factor
#print axioms WaringSiegel.WSL4Weil.geometric_denominator_polynomial_factor
