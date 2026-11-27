import WaringSiegel.WSL3MomentSystemSource
import Waring.External.GafniTao.WooleyNormalFormChange
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Exact normalization of the sparse high polynomial

For {t,...,t^(r-1),t^k}, the coefficient of t^r after translation by
an integer xi is choose(k,r) xi^(k-r).  Away from p | xi it is a unit
when p>k.  Dividing the exact Taylor tail by its p^(cr) factor and
normalizing this unit gives a literal p^c-spaced integer polynomial.
-/

noncomputable section
open Finset Polynomial GafniTao
open scoped BigOperators Classical

namespace WaringSiegel.WSL3

def sparseDegree (k r : ℕ) (j : Fin r) : ℕ :=
  if j.val + 1 = r then k else j.val + 1

def sparseValue {R : Type*} [Monoid R] (k r : ℕ) (x : R) : Fin r → R :=
  fun j => x ^ sparseDegree k r j

theorem sparseDegree_pos (k r : ℕ) (hk : 0 < k) (j : Fin r) :
    0 < sparseDegree k r j := by
  unfold sparseDegree
  split_ifs <;> omega

theorem sparseDegree_le (k r : ℕ) (hrk : r ≤ k) (j : Fin r) :
    sparseDegree k r j ≤ k := by
  unfold sparseDegree
  split_ifs <;> omega

theorem sparseValue_equations_iff {R : Type*} [CommRing R] (k r s : ℕ) (hr : 1 ≤ r)
    (x y : Fin s → R) :
    (∑ i, sparseValue k r (x i)) = (∑ i, sparseValue k r (y i)) ↔
      (∀ j, j < r → (∑ i, x i ^ j) = (∑ i, y i ^ j)) ∧
      (∑ i, x i ^ k) = (∑ i, y i ^ k) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      by_cases hj0 : j = 0
      · simp [hj0]
      · have hi : j-1 < r := by omega
        have hh := congrFun h ⟨j-1, hi⟩
        simpa only [Finset.sum_apply, sparseValue, sparseDegree,
          show j-1+1=j by omega, if_neg (by omega : j ≠ r)] using hh
    · have hh := congrFun h ⟨r-1, by omega⟩
      simpa only [Finset.sum_apply, sparseValue, sparseDegree,
        show r-1+1=r by omega, if_pos rfl] using hh
  · rintro ⟨hlo, htop⟩
    funext j
    simp only [Finset.sum_apply, sparseValue, sparseDegree]
    by_cases hj : j.val+1=r
    · simpa only [if_pos hj] using htop
    · simpa only [if_neg hj] using hlo (j.val+1) (by omega)

/-- Evaluation of any polynomial of degree below r follows from the first
r power-sum equations, including the automatically equal constant sums. -/
theorem sum_polynomial_eval_eq_of_powerSums {R : Type*} [CommRing R]
    (r s : ℕ) (x y : Fin s → R)
    (h : ∀ j, j < r → (∑ i, x i^j) = (∑ i, y i^j))
    (f : R[X]) (hf : f.natDegree < r) :
    (∑ i, f.eval (x i)) = ∑ i, f.eval (y i) := by
  rw [f.as_sum_range_C_mul_X_pow' hf]
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, ← Finset.mul_sum, h j (Finset.mem_range.mp hj)]

theorem powerSums_below_translation {R : Type*} [CommRing R]
    (r s : ℕ) (x y : Fin s → R) (ξ : R)
    (h : ∀ j, j < r → (∑ i, x i^j) = (∑ i, y i^j)) :
    ∀ j, j < r → (∑ i, (x i-ξ)^j) = ∑ i, (y i-ξ)^j := by
  intro j hj
  simpa only [eval_pow, eval_sub, eval_X, eval_C] using
    sum_polynomial_eval_eq_of_powerSums r s x y h ((X-C ξ)^j)
      ((natDegree_pow_le.trans (Nat.mul_le_mul_left j (natDegree_X_sub_C_le ξ))).trans_lt (by simpa using hj))

/-- The coefficient starting the exact Taylor tail. -/
theorem taylor_power_coeff (k r : ℕ) (ξ : ℤ) :
    (taylor ξ (X^k : ℤ[X])).coeff r = (k.choose r : ℤ)*ξ^(k-r) := by
  rw [taylor_coeff, ← monomial_one_right_eq_X_pow, hasseDeriv_monomial]
  simp

theorem polynomialTail_constant (r : ℕ) (hr : 1 ≤ r) (f : ℤ[X]) :
    (wooleyPolynomialTail r f).coeff 0 = f.coeff r := by
  have h := congrArg (fun g : ℤ[X] => g.coeff r) (wooleyPolynomial_low_add_tail r f)
  have hl : (wooleyPolynomialLowPart r f).coeff r = 0 :=
    coeff_eq_zero_of_natDegree_lt (wooleyPolynomialLowPart_natDegree_lt (by omega) f)
  simpa only [coeff_add, hl, zero_add, coeff_X_pow_mul', if_pos (le_refl r), Nat.sub_self] using h

/-- The exact high Taylor tail after dilation, with its common p^(cr)
factor omitted. Its first coefficient is a p-adic unit off xi=0. -/
def sparseTaylorTail (k r p c : ℕ) (ξ : ℤ) : ℤ[X] :=
  X^r * (wooleyPolynomialTail r (taylor ξ (X^k))).comp (C ((p : ℤ)^c)*X)

theorem sparseTaylorTail_eq_unit_monomial_add_tail (k r p c : ℕ) (hr : 1 ≤ r) (ξ : ℤ) :
    ∃ ψ : ℤ[X], sparseTaylorTail k r p c ξ =
      C ((k.choose r : ℤ)*ξ^(k-r))*X^r + C ((p : ℤ)^c)*ψ := by
  let f := wooleyPolynomialTail r (taylor ξ (X^k : ℤ[X]))
  have hf0 : f.coeff 0 = (k.choose r : ℤ)*ξ^(k-r) :=
    (polynomialTail_constant r hr _).trans (taylor_power_coeff k r ξ)
  have hdiv : X ∣ f-C ((k.choose r : ℤ)*ξ^(k-r)) := by
    rw [X_dvd_iff]
    simp only [coeff_sub, coeff_C_zero, hf0, sub_self]
  obtain ⟨g, hg⟩ := hdiv
  have hf : f = C ((k.choose r : ℤ)*ξ^(k-r)) + X*g := by rw [← hg]; ring
  refine ⟨X^(r+1)*g.comp (C ((p : ℤ)^c)*X), ?_⟩
  change X^r*f.comp (C ((p : ℤ)^c)*X) = _
  rw [hf]
  simp only [add_comp, C_comp, mul_comp, X_comp, pow_succ]
  ring

theorem sparseTaylorTail_decomposition (k r p c : ℕ) (ξ : ℤ) :
    (taylor ξ (X^k : ℤ[X])).comp (C ((p : ℤ)^c)*X) =
      (wooleyPolynomialLowPart r (taylor ξ (X^k : ℤ[X]))).comp (C ((p : ℤ)^c)*X) +
        C ((p : ℤ)^(c*r))*sparseTaylorTail k r p c ξ := by
  conv_lhs => rw [← wooleyPolynomial_low_add_tail r (taylor ξ (X^k : ℤ[X]))]
  simp only [add_comp, mul_comp, pow_comp, X_comp, mul_pow, ← C_pow, pow_mul]
  dsimp [sparseTaylorTail]
  ring

/-- The sparse high polynomial can be normalized to exactly t^r modulo
p^c, preserving its equation modulo p^B. -/
theorem sparseTaylorTail_exists_spaced_normalization (k r p c B : ℕ)
    (hp : p.Prime) (hkp : k < p) (hr : 1 ≤ r) (hrk : r ≤ k)
    (ξ : ℤ) (hξ : Nat.Coprime p ξ.natAbs) :
    ∃ φ : WooleyPolynomialSystem r, φ.Spaced p c ∧
      (∀ j : Fin r, j.val+1 < r → φ j = X^(j.val+1)) ∧
      ∃ u : ℤ, ∀ j : Fin r, j.val+1=r →
        (φ j).map (Int.castRingHom (ZMod (p^B))) =
          C (u : ZMod (p^B))*(sparseTaylorTail k r p c ξ).map (Int.castRingHom (ZMod (p^B))) := by
  let a : ℤ := (k.choose r : ℤ)*ξ^(k-r)
  have ha : Nat.Coprime p a.natAbs := by
    dsimp [a]
    simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
    exact (hp.coprime_choose_of_lt hkp hrk).mul_right (hξ.pow_right _)
  obtain ⟨u, hu⟩ := wooleySection7_exists_int_unit_inverse (L := B) ha
  obtain ⟨ψ, hψ⟩ := sparseTaylorTail_eq_unit_monomial_add_tail k r p c hr ξ
  let φ : WooleyPolynomialSystem r := fun j =>
    X^(j.val+1) + C ((p : ℤ)^c)*(if j.val+1=r then C u*ψ else 0)
  refine ⟨φ, ⟨fun j => if j.val+1=r then C u*ψ else 0, fun j => rfl⟩, ?_, u, ?_⟩
  · intro j hj
    simp only [φ, if_neg (by omega : j.val+1 ≠ r), mul_zero, add_zero]
  · intro j hj
    change (X^(j.val+1) + C ((p : ℤ)^c)*(if j.val+1=r then C u*ψ else 0)).map
      (Int.castRingHom (ZMod (p^B))) = _
    rw [if_pos hj, hj]
    rw [hψ]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Int.coe_castRingHom]
    have hu' : (u : ZMod (p^B))*(((k.choose r : ℤ)*ξ^(k-r) : ℤ) : ZMod (p^B))=1 := hu
    calc
      _ = X^r + C (((p : ℤ)^c : ℤ) : ZMod (p^B))*C (u : ZMod (p^B))*ψ.map (Int.castRingHom _) := by ring
      _ = C ((u : ZMod (p^B))*(((k.choose r : ℤ)*ξ^(k-r) : ℤ) : ZMod (p^B)))*X^r +
          C (((p : ℤ)^c : ℤ) : ZMod (p^B))*C (u : ZMod (p^B))*ψ.map (Int.castRingHom _) := by rw [hu']; simp
      _ = _ := by simp only [C_mul]; ring

#print axioms sparseTaylorTail_exists_spaced_normalization

end WaringSiegel.WSL3
