import Waring.EndgameCompletionSingularLocal
import Waring.EndgameCompletionLocalReduction

/-! # Prime-power local density identities for actual singular coefficients -/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

theorem sum_units_eq_filter (q : ℕ) [NeZero q] (F : ZMod q→ℂ) :
    (∑ a : (ZMod q)ˣ,F a)=∑ a∈(Finset.univ : Finset (ZMod q)).filter IsUnit,F a := by
  classical
  apply Finset.sum_bij (fun (a : (ZMod q)ˣ) _=>(a : ZMod q))
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.isUnit⟩
  · intro a _ b _ he
    exact Units.val_injective he
  · intro a ha
    obtain ⟨b,hb⟩ := (Finset.mem_filter.mp ha).2
    exact ⟨b,Finset.mem_univ _,hb⟩
  · intro _ _
    rfl

theorem isUnit_primepower_iff {p : ℕ} [NeZero p] (hp : p.Prime) (r : ℕ)
    (a : ZMod (p*p^r)) : IsUnit a↔¬p∣a.val := by
  calc
    _ ↔ a.val.Coprime (p*p^r) := by
      simpa only [ZMod.natCast_zmod_val] using ZMod.isUnit_iff_coprime a.val (p*p^r)
    _ ↔ a.val.Coprime p := by
      simpa only [pow_succ'] using Nat.coprime_pow_right_iff (Nat.succ_pos r) a.val p
    _ ↔ _ := by rw [Nat.coprime_comm,hp.coprime_iff_not_dvd]

theorem productSingularTerm_modulus_one (k u v L : ℕ) (n : ℤ) (a : ZMod 1) :
    productSingularTerm 1 k u v L n a=1 := by
  have hc (b : ZMod 1) : ZMod.stdAddChar b=1 := by
    rw [Subsingleton.elim b 0,AddChar.map_zero_eq_one]
  simp [productSingularTerm,ordinaryCompleteMean,productCompleteMean,
    completeMonomialSumMod,productCompleteSum,hc]

theorem productSingularCoefficient_one (k u v L : ℕ) (n : ℤ) :
    productSingularCoefficient k u v L n 1=1 := by
  rw [productSingularCoefficient_nezero]
  change (∑ a : (ZMod 1)ˣ,productSingularTerm 1 k u v L n a)=1
  simp [productSingularTerm_modulus_one]

theorem fullProductSingularCoefficient_one (k u v L : ℕ) (n : ℤ) :
    fullProductSingularCoefficient 1 k u v L n=1 := by
  simp [fullProductSingularCoefficient,productSingularTerm_modulus_one]

theorem fullProductSingularCoefficient_prime_succ {p : ℕ} [NeZero p] (hp : p.Prime)
    (r k u v L : ℕ) (n : ℤ) :
    fullProductSingularCoefficient (p^(r+1)) k u v L n=
      fullProductSingularCoefficient (p^r) k u v L n+
        productSingularCoefficient k u v L n (p^(r+1)) := by
  classical
  simp only [pow_succ']
  have hnonunit : (∑ a∈(Finset.univ : Finset (ZMod (p*p^r))).filter (fun a=>p∣a.val),
      productSingularTerm (p*p^r) k u v L n a)=
        fullProductSingularCoefficient (p^r) k u v L n := by
    rw [sum_zmod_filter_dvd (p*p^r) p (p^r) hp.pos rfl]
    simp_rw [Nat.cast_mul,productSingularTerm_multiple,map_natCast]
    exact (sum_zmod_eq_sum_range (p^r) (productSingularTerm (p^r) k u v L n)).symm
  have hunit : (∑ a∈(Finset.univ : Finset (ZMod (p*p^r))).filter (fun a=>¬p∣a.val),
      productSingularTerm (p*p^r) k u v L n a)=
        productSingularCoefficient k u v L n (p*p^r) := by
    rw [productSingularCoefficient_nezero]
    change _=∑ a : (ZMod (p*p^r))ˣ,productSingularTerm (p*p^r) k u v L n a
    rw [sum_units_eq_filter]
    exact Finset.sum_congr (Finset.filter_congr (fun a _=>(isUnit_primepower_iff hp r a).symm))
      (fun _ _=>rfl)
  change (∑ a : ZMod (p*p^r),productSingularTerm (p*p^r) k u v L n a)=_
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun a : ZMod (p*p^r)=>p∣a.val)]
  rw [hnonunit,hunit]

/-- Every finite prime-power series is an actual normalized local count. -/
theorem productSingularCoefficient_prime_partial_sum {p : ℕ} [NeZero p] (hp : p.Prime)
    (r k u v L : ℕ) (n : ℤ) :
    (∑ j∈Finset.range (r+1),productSingularCoefficient k u v L n (p^j))=
      fullProductSingularCoefficient (p^r) k u v L n := by
  induction r with
  | zero => simp [productSingularCoefficient_one,fullProductSingularCoefficient_one]
  | succ r ih =>
      rw [Finset.sum_range_succ,ih,fullProductSingularCoefficient_prime_succ hp]

#print axioms productSingularCoefficient_prime_partial_sum
end Waring.EndgameCompletion
