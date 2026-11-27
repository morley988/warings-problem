import Waring.SeedCompletionSparseDiagonal
import Waring.PolicyCompletionHolder
import Mathlib.Algebra.Polynomial.Roots

/-!
# A finite family of integer vector constraints encoded by one frequency

For any finite set of integer vectors, a single integral linear functional
detects exactly which of those vectors are zero. Its coefficients need no
quantitative bound: exact Fourier orthogonality is independent of frequency.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseWeighted

def code {J : ℕ} (b : ℤ) (v : Fin J → ℤ) : ℤ :=
  ∑ r, v r * b ^ r.val

def codePolynomial {J : ℕ} (v : Fin J → ℤ) : Polynomial ℤ :=
  ∑ r, Polynomial.monomial r.val (v r)

theorem codePolynomial_coeff {J : ℕ} (v : Fin J → ℤ) (r : Fin J) :
    (codePolynomial v).coeff r.val = v r := by
  classical
  simp only [codePolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single r]
  · simp
  · intro i hi hir
    have hval : i.val ≠ r.val := fun he => hir (Fin.ext he)
    simp [hval]
  · simp

theorem codePolynomial_ne_zero {J : ℕ} {v : Fin J → ℤ} (hv : v ≠ 0) :
    codePolynomial v ≠ 0 := by
  intro he
  apply hv
  funext r
  have hh := congrArg (fun q : Polynomial ℤ => q.coeff r.val) he
  simpa only [codePolynomial_coeff, Polynomial.coeff_zero, Pi.zero_apply] using hh

theorem codePolynomial_eval {J : ℕ} (v : Fin J → ℤ) (b : ℤ) :
    (codePolynomial v).eval b = code b v := by
  classical
  simp [codePolynomial, code, Polynomial.eval_finset_sum, Polynomial.eval_monomial]

theorem exists_code_detecting_zero {J : ℕ} (F : Finset (Fin J → ℤ)) :
    ∃ b : ℤ, ∀ v ∈ F, code b v = 0 ↔ v = 0 := by
  classical
  let G := F.filter (fun v => v ≠ 0)
  let q : Polynomial ℤ := ∏ v ∈ G, codePolynomial v
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact codePolynomial_ne_zero (Finset.mem_filter.mp hv).2
  have he : ∃ b : ℤ, q.eval b ≠ 0 := by
    by_contra! hh
    exact hq (Polynomial.zero_of_eval_zero q hh)
  obtain ⟨b,hb⟩ := he
  refine ⟨b,?_⟩
  intro v hv
  constructor
  · intro hc
    by_contra hn
    have hvg : v ∈ G := Finset.mem_filter.mpr ⟨hv,hn⟩
    apply hb
    dsimp [q]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hvg (by simpa [codePolynomial_eval] using hc)
  · rintro rfl
    simp [code]

theorem code_add {J : ℕ} (b : ℤ) (v w : Fin J → ℤ) :
    code b (v+w) = code b v + code b w := by
  simp [code, add_mul, Finset.sum_add_distrib]

theorem code_sub {J : ℕ} (b : ℤ) (v w : Fin J → ℤ) :
    code b (v-w) = code b v - code b w := by
  simp [code, sub_mul, Finset.sum_sub_distrib]

theorem code_sum {J : ℕ} {α : Type*} (b : ℤ) (A : Finset α)
    (v : α → Fin J → ℤ) :
    code b (∑ a ∈ A, v a) = ∑ a ∈ A, code b (v a) := by
  classical
  simp only [code, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

#print axioms exists_code_detecting_zero
end Waring.SeedCompletionSparseWeighted
