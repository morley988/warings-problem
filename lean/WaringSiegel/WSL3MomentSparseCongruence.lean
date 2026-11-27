import WaringSiegel.WSL3MomentSparsePolynomial

/-!
# Sparse equations imply the normalized p-spaced equations

Every division has an explicit prime-power modulus cost.  Original nodes
have the form p^e (xi+p^c z), with p not dividing xi; a working depth
L >= B+k(e+c) leaves all r normalized equations valid modulo p^B.
-/

noncomputable section
open Finset Polynomial GafniTao
open scoped BigOperators Classical

namespace WaringSiegel.WSL3

theorem int_sum_cast_eq_iff_dvd {s : ℕ} (p B : ℕ) (x y : Fin s → ℤ) :
    (∑ i, (x i : ZMod (p^B))) = (∑ i, (y i : ZMod (p^B))) ↔
      (p : ℤ)^B ∣ (∑ i, x i)-(∑ i, y i) := by
  rw [← sub_eq_zero, ← Int.cast_sum, ← Int.cast_sum, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]

theorem primePower_cancel_to_depth {p d L B : ℕ} {z : ℤ} (hp : p ≠ 0)
    (hdepth : d+B ≤ L) (hdiv : (p : ℤ)^L ∣ (p : ℤ)^d*z) :
    (p : ℤ)^B ∣ z := by
  have hd : (p : ℤ)^(d+B) ∣ (p : ℤ)^d*1*z := by
    simpa only [mul_one] using dvd_trans (pow_dvd_pow (p : ℤ) hdepth) hdiv
  exact wooleySection7_primePower_unit_cancel_dvd hp (by simp) hd

theorem integer_polynomial_sums_congr {s : ℕ} (p B r : ℕ) (x y : Fin s → ℤ)
    (h : ∀ j, j < r → (p : ℤ)^B ∣ (∑ i, x i^j)-(∑ i, y i^j))
    (f : ℤ[X]) (hf : f.natDegree < r) :
    (p : ℤ)^B ∣ (∑ i, f.eval (x i))-(∑ i, f.eval (y i)) := by
  apply (int_sum_cast_eq_iff_dvd p B _ _).mp
  have hpow : ∀ j, j < r →
      (∑ i, (x i : ZMod (p^B))^j) = ∑ i, (y i : ZMod (p^B))^j := by
    intro j hj
    simpa only [Int.cast_pow] using (int_sum_cast_eq_iff_dvd p B _ _).mpr (h j hj)
  have hfmap : (f.map (Int.castRingHom (ZMod (p^B)))).natDegree < r :=
    (natDegree_map_le).trans_lt hf
  have hh := sum_polynomial_eval_eq_of_powerSums r s
    (fun i => (x i : ZMod (p^B))) (fun i => (y i : ZMod (p^B))) hpow
    (f.map (Int.castRingHom (ZMod (p^B)))) hfmap
  simpa only [eval_intCast_map] using hh

theorem sparseTaylorTail_eval_decomposition (k r p c : ℕ) (ξ z : ℤ) :
    (ξ+(p : ℤ)^c*z)^k =
      (wooleyPolynomialLowPart r (taylor ξ (X^k : ℤ[X]))).eval ((p : ℤ)^c*z) +
        (p : ℤ)^(c*r)*(sparseTaylorTail k r p c ξ).eval z := by
  have h := congrArg (fun f : ℤ[X] => f.eval z) (sparseTaylorTail_decomposition k r p c ξ)
  simpa only [eval_comp, eval_mul, eval_C, eval_X, taylor_eval, eval_pow,
    eval_add, add_comm ((p : ℤ)^c*z) ξ] using h

/-- Uniform sparse normalization on an arbitrary nonzero p-adic annulus.
The resulting system is fixed before the tuple length and tuple are given. -/
theorem sparse_equations_normalize_on_progression (k r p c B : ℕ)
    (hp : p.Prime) (hkp : k < p) (hr : 1 ≤ r) (hrk : r ≤ k)
    (ξ : ℤ) (hξ : Nat.Coprime p ξ.natAbs) :
    ∃ φ : WooleyPolynomialSystem r, φ.Spaced p c ∧
      ∀ (e L s : ℕ), B+k*(e+c) ≤ L → ∀ x y : Fin s → ℤ,
        (∑ i, sparseValue k r (((p : ℤ)^e*(ξ+(p : ℤ)^c*x i) : ℤ) : ZMod (p^L))) =
          (∑ i, sparseValue k r (((p : ℤ)^e*(ξ+(p : ℤ)^c*y i) : ℤ) : ZMod (p^L))) →
        (∑ i, fun j => (((φ j).eval (x i) : ℤ) : ZMod (p^B))) =
          (∑ i, fun j => (((φ j).eval (y i) : ℤ) : ZMod (p^B))) := by
  obtain ⟨φ, hφ, hlowφ, u, htopφ⟩ :=
    sparseTaylorTail_exists_spaced_normalization k r p c B hp hkp hr hrk ξ hξ
  refine ⟨φ, hφ, ?_⟩
  intro e L s hL x y h
  let M := B+c*r
  let xx : Fin s → ℤ := fun i => ξ+(p : ℤ)^c*x i
  let yy : Fin s → ℤ := fun i => ξ+(p : ℤ)^c*y i
  have heq := (sparseValue_equations_iff k r s hr _ _).mp h
  have hscaled (j : ℕ) (hjk : j ≤ k)
      (hpower : (∑ i, (((p : ℤ)^e*xx i : ℤ) : ZMod (p^L))^j) =
        ∑ i, (((p : ℤ)^e*yy i : ℤ) : ZMod (p^L))^j) :
      (p : ℤ)^M ∣ (∑ i, xx i^j)-(∑ i, yy i^j) := by
    have hdiv : (p : ℤ)^L ∣ (∑ i, ((p : ℤ)^e*xx i)^j)-
        (∑ i, ((p : ℤ)^e*yy i)^j) := by
      apply (int_sum_cast_eq_iff_dvd p L _ _).mp
      simpa only [Int.cast_pow] using hpower
    simp_rw [mul_pow, ← pow_mul] at hdiv
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub] at hdiv
    apply primePower_cancel_to_depth hp.ne_zero (B := M) _ hdiv
    dsimp [M]
    nlinarith
  have hu : ∀ j, j < r → (p : ℤ)^M ∣ (∑ i, xx i^j)-(∑ i, yy i^j) :=
    fun j hj => hscaled j (by omega) (heq.1 j hj)
  have huk := hscaled k le_rfl heq.2
  have hshift : ∀ j, j < r →
      (p : ℤ)^M ∣ (∑ i, ((p : ℤ)^c*x i)^j)-(∑ i, ((p : ℤ)^c*y i)^j) := by
    intro j hj
    have hjdeg : ((X-C ξ)^j : ℤ[X]).natDegree < r := by
      simpa only [(monic_X_sub_C ξ).natDegree_pow, natDegree_X_sub_C, mul_one] using hj
    have hh := integer_polynomial_sums_congr p M r xx yy hu ((X-C ξ)^j) hjdeg
    simpa only [eval_pow, eval_sub, eval_X, eval_C, xx, yy, add_sub_cancel_left] using hh
  have hzlow (j : ℕ) (hj : j < r) :
      (∑ i, (x i : ZMod (p^B))^j) = ∑ i, (y i : ZMod (p^B))^j := by
    have hd := hshift j hj
    simp_rw [mul_pow, ← pow_mul] at hd
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub] at hd
    have hb : (p : ℤ)^B ∣ (∑ i, x i^j)-(∑ i, y i^j) :=
      primePower_cancel_to_depth hp.ne_zero (by dsimp [M]; nlinarith) hd
    simpa only [Int.cast_pow] using (int_sum_cast_eq_iff_dvd p B _ _).mpr hb
  let f := wooleyPolynomialLowPart r (taylor ξ (X^k : ℤ[X]))
  have hfd : f.natDegree < r := wooleyPolynomialLowPart_natDegree_lt (by omega) _
  have hflow := integer_polynomial_sums_congr p M r
    (fun i => (p : ℤ)^c*x i) (fun i => (p : ℤ)^c*y i) hshift f hfd
  have hdecomp : (∑ i, xx i^k)-(∑ i, yy i^k) =
      ((∑ i, f.eval ((p : ℤ)^c*x i))-(∑ i, f.eval ((p : ℤ)^c*y i))) +
        (p : ℤ)^(c*r)*((∑ i, (sparseTaylorTail k r p c ξ).eval (x i))-
          (∑ i, (sparseTaylorTail k r p c ξ).eval (y i))) := by
    dsimp only [xx, yy]
    simp_rw [sparseTaylorTail_eval_decomposition k r p c ξ]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, f]
    ring
  rw [hdecomp] at huk
  have hg : (p : ℤ)^B ∣
      (∑ i, (sparseTaylorTail k r p c ξ).eval (x i))-
        (∑ i, (sparseTaylorTail k r p c ξ).eval (y i)) := by
    apply primePower_cancel_to_depth (d := c*r) (L := M) hp.ne_zero (by dsimp [M]; omega)
    have hd := dvd_sub huk hflow
    simpa only [add_sub_cancel_left] using hd
  have hgeq := (int_sum_cast_eq_iff_dvd p B _ _).mpr hg
  funext j
  simp only [Finset.sum_apply]
  by_cases hj : j.val+1=r
  · have hmap := htopφ j hj
    have hv (z : ℤ) : (((φ j).eval z : ℤ) : ZMod (p^B)) =
        (u : ZMod (p^B))*(((sparseTaylorTail k r p c ξ).eval z : ℤ) : ZMod (p^B)) := by
      have he := congrArg (fun f : (ZMod (p^B))[X] => f.eval (z : ZMod (p^B))) hmap
      simpa only [eval_mul, eval_C, eval_intCast_map] using he
    simp_rw [hv, ← Finset.mul_sum, hgeq]
  · rw [hlowφ j (by omega)]
    simpa only [eval_pow, eval_X, Int.cast_pow] using hzlow (j.val+1) (by omega)

#print axioms sparse_equations_normalize_on_progression

end WaringSiegel.WSL3
