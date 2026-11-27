import Waring.EndgameCompletionSingularCRT
import Waring.LocalSolubilityProduct

/-! # Exact finite orthogonality for product singular local densities -/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

theorem stdAddChar_finset_sum {ι : Type*} (q : ℕ) [NeZero q]
    (S : Finset ι) (f : ι→ZMod q) :
    ZMod.stdAddChar (∑ i∈S,f i)=∏ i∈S,ZMod.stdAddChar (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

theorem completeMonomialSumMod_power (q k u : ℕ) [NeZero q] (a : ZMod q) :
    completeMonomialSumMod q k a^u=
      ∑ x : Fin u→ZMod q,ZMod.stdAddChar (a*(∑ i,x i^k)) := by
  rw [completeMonomialSumMod,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum,stdAddChar_finset_sum]

theorem productCompleteSum_power (q k v L : ℕ) [NeZero q] (a : ZMod q) :
    productCompleteSum q k L a^v=
      ∑ y : Fin v→Fin L→ZMod q,ZMod.stdAddChar (a*(∑ j,(∏ l,y j l)^k)) := by
  rw [productCompleteSum,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum,stdAddChar_finset_sum]

def fullProductSingularCoefficient (q k u v L : ℕ) [NeZero q] (n : ℤ) : ℂ :=
  ∑ a : ZMod q,productSingularTerm q k u v L n a

def mixedLocalForm {q : ℕ} (k u v L : ℕ)
    (z : (Fin u→ZMod q) × (Fin v→Fin L→ZMod q)) : ZMod q :=
  (∑ i,z.1 i^k)+(∑ j,(∏ l,z.2 j l)^k)

theorem productSingularTerm_expansion (q k u v L : ℕ) [NeZero q] (n : ℤ) (a : ZMod q) :
    productSingularTerm q k u v L n a=
      (∑ z : (Fin u→ZMod q) × (Fin v→Fin L→ZMod q),
        ZMod.stdAddChar (a*(mixedLocalForm k u v L z-(n : ZMod q))))/(q : ℂ)^(u+L*v) := by
  unfold productSingularTerm ordinaryCompleteMean productCompleteMean
  rw [div_pow,div_pow,← mul_div_mul_comm,← pow_mul,← pow_add,div_mul_eq_mul_div]
  congr 1
  rw [completeMonomialSumMod_power,productCompleteSum_power,
    Fintype.sum_mul_sum,Finset.sum_mul,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [← AddChar.map_add_eq_mul,← AddChar.map_add_eq_mul]
  congr 1
  dsimp only [mixedLocalForm]
  ring

theorem fullProductSingularCoefficient_eq_count (q k u v L : ℕ) [NeZero q] (n : ℤ) :
    fullProductSingularCoefficient q k u v (L+1) n=
      (q : ℂ)*(LocalSolubility.productPowerSolutions k u v L q n).card/
        (q : ℂ)^(u+(L+1)*v) := by
  classical
  unfold fullProductSingularCoefficient
  simp_rw [productSingularTerm_expansion]
  rw [← Finset.sum_div,Finset.sum_comm]
  congr 1
  calc
    _ = ∑ z : (Fin u→ZMod q) × (Fin v→Fin (L+1)→ZMod q),
        if mixedLocalForm k u v (L+1) z=(n : ZMod q) then (q : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      simp_rw [mul_comm _ (mixedLocalForm k u v (L+1) z-(n : ZMod q))]
      simp only [stdAddChar_mul_sum,sub_eq_zero]
    _ = _ := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_comm]
      rfl

#print axioms fullProductSingularCoefficient_eq_count
end Waring.EndgameCompletion
