import Waring.DifferenceSquaresFibers
import Waring.DivisorBound
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Ring.GeomSum

/-!
# Nonzero positive-variable power-difference fibers

For k>=2, fixing the nonzero difference m-n determines a pair of nonnegative
natural variables from the value m^k-n^k. The proof establishes the required
strict monotonicity of the difference polynomial. Divisor injections then
bound the actual fibers of h^2*(m^k-n^k), including the depth-six degree-eight
auxiliary with k=16. Arbitrarily small power losses come from the proved
divisor theorem, not an assumed counting estimate.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PowerDifferenceFibers
open DifferenceSquaresFibers

/-- Strict monotonicity of the remaining difference polynomial in its
nonnegative base variable. The nonzero shift is positive in this statement. -/
theorem power_increment_strictMonoOn (k : ℕ) (hk : 2 ≤ k) {d : ℝ} (hd : 0 < d) :
    StrictMonoOn (fun x : ℝ => (x+d)^k-x^k) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    (((continuous_id.add continuous_const).pow k).sub (continuous_id.pow k)).continuousOn
  intro x hx
  have hx0 : 0 ≤ x := Set.mem_Ici.mp (interior_subset hx)
  have hderiv := (((hasDerivAt_id x).add_const d).pow k).sub ((hasDerivAt_id x).pow k)
  have hderiv' : HasDerivAt (fun y : ℝ => (y+d)^k-y^k)
      ((k : ℝ)*(x+d)^(k-1)-(k : ℝ)*x^(k-1)) x := by
    simpa only [Pi.pow_apply,Pi.sub_apply,id_eq,mul_one] using hderiv
  simp only [id_eq]
  rw [hderiv'.deriv]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp : x^(k-1) < (x+d)^(k-1) :=
    pow_lt_pow_left₀ (by linarith) hx0 (by omega)
  nlinarith

private theorem pair_eq_of_positive_shift (k : ℕ) (hk : 2 ≤ k)
    {m n m' n' : ℕ} (hpos : n < m)
    (hp : (m : ℤ)^k-(n : ℤ)^k=(m' : ℤ)^k-(n' : ℤ)^k)
    (hd : (m : ℤ)-n=(m' : ℤ)-n') : (m,n)=(m',n') := by
  let d : ℝ := (m : ℝ)-n
  have hdpos : 0 < d := by dsimp [d]; exact sub_pos.mpr (by exact_mod_cast hpos)
  have hdR : (m : ℝ)-n=(m' : ℝ)-n' := by exact_mod_cast hd
  have hpR : (m : ℝ)^k-(n : ℝ)^k=(m' : ℝ)^k-(n' : ℝ)^k := by exact_mod_cast hp
  have hm : (n : ℝ)+d=m := by dsimp [d]; ring
  have hm' : (n' : ℝ)+d=m' := by dsimp [d]; linarith
  have hnR : (n : ℝ)=(n' : ℝ) :=
    (power_increment_strictMonoOn k hk hdpos).injOn
      (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by positivity))
      (by simpa only [hm,hm'] using hpR)
  have hn : n=n' := by exact_mod_cast hnR
  have hmm : m=m' := by omega
  exact Prod.ext hmm hn

/-- Equality of a nonzero power difference and of the signed first difference
forces equality of both natural variables. Negative differences are included. -/
theorem pair_eq_of_difference_eq (k : ℕ) (hk : 2 ≤ k)
    {m n m' n' : ℕ} (hnz : (m : ℤ)^k-(n : ℤ)^k ≠ 0)
    (hp : (m : ℤ)^k-(n : ℤ)^k=(m' : ℤ)^k-(n' : ℤ)^k)
    (hd : (m : ℤ)-n=(m' : ℤ)-n') : (m,n)=(m',n') := by
  have hne : m ≠ n := by intro h; subst n; simp at hnz
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hswap := pair_eq_of_positive_shift k hk hlt
      (show (n : ℤ)^k-(m : ℤ)^k=(n' : ℤ)^k-(m' : ℤ)^k by linarith)
      (show (n : ℤ)-m=(n' : ℤ)-m' by omega)
    simpa using congrArg Prod.swap hswap
  · exact pair_eq_of_positive_shift k hk hgt hp hd

/-- The actual finite fiber of a fixed nonzero kth-power difference. -/
theorem power_difference_fiber_card_le (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (ℕ × ℕ)) {b : ℤ} (hb : b ≠ 0)
    (hS : ∀ x ∈ S, (x.1 : ℤ)^k-(x.2 : ℤ)^k=b) :
    S.card ≤ 2*b.natAbs.divisors.card := by
  apply (Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => (x.1 : ℤ)-x.2) ?_ ?_).trans
    (card_signedDivisors_le b)
  · intro x hx
    apply mem_signedDivisors hb
    rw [← hS x hx]
    exact sub_dvd_pow_sub_pow _ _ _
  · intro x hx y hy hdiff
    exact pair_eq_of_difference_eq k hk (by rw [hS x hx]; exact hb)
      ((hS x hx).trans (hS y hy).symm) hdiff

@[ext] structure Block where
  h : ℕ
  m : ℕ
  n : ℕ
  deriving DecidableEq, Repr

def blockValue (k : ℕ) (x : Block) : ℤ :=
  (x.h : ℤ)^2*((x.m : ℤ)^k-(x.n : ℤ)^k)

theorem block_h_ne_zero (k : ℕ) (x : Block) {b : ℤ} (hb : b ≠ 0)
    (hx : blockValue k x=b) : x.h ≠ 0 := by
  intro hz
  apply hb
  rw [← hx,blockValue,hz]
  simp

/-- A nonzero weighted difference is encoded by a positive divisor h and a
signed divisor m-n of the fixed right-hand side. -/
theorem block_fiber_card_le (k : ℕ) (hk : 2 ≤ k) (S : Finset Block)
    {b : ℤ} (hb : b ≠ 0) (hS : ∀ x ∈ S, blockValue k x=b) :
    S.card ≤ 2*b.natAbs.divisors.card^2 := by
  let code : Block → ℕ × ℤ := fun x => (x.h,(x.m : ℤ)-x.n)
  have hm : ∀ x ∈ S, code x ∈ b.natAbs.divisors ×ˢ signedDivisors b := by
    intro x hx
    have hv := hS x hx
    apply Finset.mem_product.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      refine ⟨Int.natCast_dvd.mp ?_,Int.natAbs_ne_zero.mpr hb⟩
      rw [← hv]
      refine ⟨(x.h : ℤ)*((x.m : ℤ)^k-(x.n : ℤ)^k), ?_⟩
      unfold blockValue
      ring
    · apply mem_signedDivisors hb
      rw [← hv,blockValue]
      exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ _) _
  have hinj : Set.InjOn code (S : Set Block) := by
    intro x hx y hy hcode
    have hh : x.h=y.h := congrArg Prod.fst hcode
    have hd : (x.m : ℤ)-x.n=(y.m : ℤ)-y.n := congrArg Prod.snd hcode
    have hxv := hS x hx
    have hyv := hS y hy
    have hh0 : (x.h : ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast block_h_ne_zero k x hb hxv)
    have hp : (x.m : ℤ)^k-(x.n : ℤ)^k=(y.m : ℤ)^k-(y.n : ℤ)^k := by
      apply mul_left_cancel₀ hh0
      simpa only [blockValue,← hh] using hxv.trans hyv.symm
    have hnz : (x.m : ℤ)^k-(x.n : ℤ)^k ≠ 0 := by
      intro hz
      apply hb
      rw [← hxv,blockValue,hz,mul_zero]
    have hmn := pair_eq_of_difference_eq k hk hnz hp hd
    exact Block.ext hh (congrArg Prod.fst hmn) (congrArg Prod.snd hmn)
  have hcard := Finset.card_le_card_of_injOn code hm hinj
  rw [Finset.card_product] at hcard
  have hsign := card_signedDivisors_le b
  nlinarith

/-- Uniform subpower multiplicity for actual weighted difference fibers.
The same constant works for all k>=2 and all finite block families. -/
theorem block_fiber_card_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → ∀ S : Finset Block,
      ∀ b : ℤ, b ≠ 0 → (∀ x ∈ S, blockValue k x=b) →
        (S.card : ℝ) ≤ C*(b.natAbs : ℝ)^ε := by
  obtain ⟨D,hD,hdiv⟩ := DivisorBound.divisor_count_le_rpow (show 0 < ε/3 by linarith)
  refine ⟨2*D^2,by positivity,?_⟩
  intro k hk S b hb hS
  have hbpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hcard : (S.card : ℝ) ≤ 2*(b.natAbs.divisors.card : ℝ)^2 := by
    exact_mod_cast block_fiber_card_le k hk S hb hS
  calc
    _ ≤ 2*(b.natAbs.divisors.card : ℝ)^2 := hcard
    _ ≤ 2*(D*(b.natAbs : ℝ)^(ε/3))^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (hdiv _ hbpos) _) (by norm_num)
    _ = (2*D^2)*(b.natAbs : ℝ)^((ε/3)*2) := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity)]
      norm_num
      ring
    _ ≤ (2*D^2)*(b.natAbs : ℝ)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hbpos) (by linarith)) (by positivity)

/-- The standard P^epsilon multiplicity form under a fixed polynomial size
bound on the nonzero right-hand side. -/
theorem block_fiber_card_le_polynomial {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ k : ℕ, 2 ≤ k →
      ∀ S : Finset Block, ∀ b : ℤ, b ≠ 0 → (b.natAbs : ℝ) ≤ P^B →
      (∀ x ∈ S, blockValue k x=b) → (S.card : ℝ) ≤ C*P^ε := by
  let δ : ℝ := ε/(B+1)
  have hB1 : 0 < B+1 := by linarith
  have hδ : 0 < δ := div_pos hε hB1
  have hBδ : B*δ ≤ ε := by
    have hid : δ*(B+1)=ε := div_mul_cancel₀ ε hB1.ne'
    nlinarith
  obtain ⟨C,hC,hbound⟩ := block_fiber_card_le_rpow hδ
  refine ⟨C,hC,?_⟩
  intro P hP k hk S b hb hbP hS
  apply (hbound k hk S b hb hS).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  calc
    (b.natAbs : ℝ)^δ ≤ (P^B)^δ := Real.rpow_le_rpow (by positivity) hbP hδ.le
    _ = P^(B*δ) := (Real.rpow_mul (zero_le_one.trans hP) _ _).symm
    _ ≤ P^ε := Real.rpow_le_rpow_of_exponent_le hP hBδ

#print axioms power_difference_fiber_card_le
#print axioms block_fiber_card_le
#print axioms block_fiber_card_le_polynomial
end Waring.PowerDifferenceFibers
