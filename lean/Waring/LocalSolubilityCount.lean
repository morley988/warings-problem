import Waring.LocalSolubilityLifting
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Ring.GeomSum

/-! # A literal lower bound for local representation counts

One variable lifts the target; all remaining variables vary freely in
their base congruence classes. The resulting injection proves the local
density lower bound, rather than merely asserting existence of a solution.
-/

noncomputable section
open scoped BigOperators
namespace Waring.LocalSolubility

def powerSolutions (k s q : ℕ) [NeZero q] (n : ℤ) : Finset (Fin s → ZMod q) :=
  Finset.univ.filter (fun x => ∑ i,(x i)^k=(n : ZMod q))

theorem powerSolutions_card_congr_modulus {q q' : ℕ} [NeZero q] [NeZero q']
    (h : q=q') (k s : ℕ) (n : ℤ) :
    (powerSolutions k s q n).card=(powerSolutions k s q' n).card := by
  subst q'
  rfl

theorem residueProgression_injective {B M : ℕ} (hB : 0 < B) (hM : 0 < M) (a : ℤ) :
    Function.Injective (fun t : Fin M => ((a+(B : ℤ)*(t.val : ℤ) : ℤ) : ZMod (B*M))) := by
  intro i j hij
  have hdiv := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (B*M)).mp hij
  have hd : (B : ℤ)*(M : ℤ) ∣ (B : ℤ)*((j.val : ℤ)-(i.val : ℤ)) := by
    convert hdiv using 1 <;> push_cast <;> ring
  have hsmall : (M : ℤ) ∣ (j.val : ℤ)-(i.val : ℤ) :=
    (mul_dvd_mul_iff_left (show (B : ℤ) ≠ 0 by exact_mod_cast hB.ne')).mp hd
  have heq : (i.val : ZMod M)=(j.val : ZMod M) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (i.val : ℤ) (j.val : ℤ) M).mpr hsmall
  have hmod := (ZMod.natCast_eq_natCast_iff' i.val j.val M).mp heq
  apply Fin.ext
  simpa only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hmod

theorem base_congruence_for_free_coordinates {k s B : ℕ} (a n : ℤ) (b : Fin s → ℤ)
    (hbase : (B : ℤ) ∣ a^k+(∑ i,(b i)^k)-n) (v : Fin s → ℤ) :
    (B : ℤ) ∣ a^k-(n-∑ i,(b i+(B : ℤ)*v i)^k) := by
  have hd : (B : ℤ) ∣ ∑ i,((b i+(B : ℤ)*v i)^k-(b i)^k) := by
    apply Finset.dvd_sum
    intro i _
    apply (show (B : ℤ) ∣ (b i+(B : ℤ)*v i)-b i from ⟨v i,by ring⟩).trans
    exact sub_dvd_pow_sub_pow _ _ k
  have hh := dvd_add hbase hd
  convert hh using 1
  rw [Finset.sum_sub_distrib]
  ring

/-- A one-variable lifting theorem yields at least M^s actual solutions
modulo B*M in s+1 variables, with a constant independent of the target. -/
theorem powerSolutions_card_lower_of_lifting {k s B M : ℕ}
    (hB : 0 < B) (hM : 0 < M) (a n : ℤ) (b : Fin s → ℤ)
    (hbase : (B : ℤ) ∣ a^k+(∑ i,(b i)^k)-n)
    (hsolve : ∀ target : ℤ,(B : ℤ) ∣ a^k-target →
      ∃ y : ℤ,((B*M : ℕ) : ℤ) ∣ y^k-target) :
    letI : NeZero (B*M) := ⟨(Nat.mul_pos hB hM).ne'⟩
    M^s ≤ (powerSolutions k (s+1) (B*M) n).card := by
  letI : NeZero (B*M) := ⟨(Nat.mul_pos hB hM).ne'⟩
  classical
  let target := fun v : Fin s → Fin M => n-∑ i,(b i+(B : ℤ)*(v i).val)^k
  have hex : ∀ v : Fin s → Fin M,∃ y : ℤ,((B*M : ℕ) : ℤ) ∣ y^k-target v := by
    intro v
    exact hsolve (target v) (base_congruence_for_free_coordinates a n b hbase (fun i => (v i).val))
  choose y hy using hex
  let f : (Fin s → Fin M) → Fin (s+1) → ZMod (B*M) :=
    fun v => Fin.cons (y v : ZMod (B*M)) (fun i => ((b i+(B : ℤ)*(v i).val : ℤ) : ZMod (B*M)))
  have hmap : Set.MapsTo f (Finset.univ : Finset (Fin s → Fin M))
      (powerSolutions k (s+1) (B*M) n) := by
    intro v _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd ((y v)^k-target v) (B*M)).mpr (hy v)
    dsimp [target] at hc
    push_cast at hc
    change (y v : ZMod (B*M))^k-((n : ZMod (B*M))-
      ∑ i,((b i : ZMod (B*M))+(B : ZMod (B*M))*(v i).val)^k)=0 at hc
    simp only [f,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    linear_combination hc
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin s → Fin M)) := by
    intro v _ w _ hvw
    funext i
    apply residueProgression_injective hB hM (b i)
    exact congrArg (fun z : Fin (s+1) → ZMod (B*M) => z i.succ) hvw
  have hh := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin] using hh

#print axioms powerSolutions_card_lower_of_lifting
end Waring.LocalSolubility
