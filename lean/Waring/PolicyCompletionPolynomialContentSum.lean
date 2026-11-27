import Waring.PolicyCompletionPolynomialPrimePower

/-! # Exact content reduction of arbitrary complete polynomial sums -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialContentSum
open Polynomial EndgameCompletion PolicyCompletionPolynomialRecursion
  PolicyCompletionPolynomialContent PolicyCompletionPolynomialResidues
  PolicyCompletionPolynomialBranch PolicyCompletionPolynomialPrimePower

theorem integerPolynomialSum_add_C (q : ℕ) [NeZero q] (f : Polynomial ℤ) (a : ℤ) :
    integerPolynomialSum q (f+C a)=
      integerPolynomialSum q f*ZMod.stdAddChar (a : ZMod q) := by
  rw [integerPolynomialSum_eq_range,integerPolynomialSum_eq_range,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Polynomial.eval_add,Polynomial.eval_C,Int.cast_add,AddChar.map_add_eq_mul]

theorem norm_integerPolynomialSum_add_C (q : ℕ) [NeZero q] (f : Polynomial ℤ) (a : ℤ) :
    ‖integerPolynomialSum q (f+C a)‖=‖integerPolynomialSum q f‖ := by
  rw [integerPolynomialSum_add_C,norm_mul]
  simp [ZMod.stdAddChar_apply]

theorem integerPolynomialSum_content_reduced {p : ℕ} [Fact p.Prime]
    (m v : ℕ) (hv : v ≤ m) (g : Polynomial ℤ) :
    integerPolynomialSum (p^m) (C ((p : ℤ)^v)*g)=
      ((p^v : ℕ) : ℂ)*integerPolynomialSum (p^(m-v)) g := by
  rw [integerPolynomialSum_eq_range]
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  simp_rw [stdAddChar_primepower_factor m v hv]
  have hper : Function.Periodic
      (fun y : ℕ => ZMod.stdAddChar ((g.eval (y : ℤ) : ℤ) : ZMod (p^(m-v))))
        (p^(m-v)) := by
    intro y
    change ZMod.stdAddChar ((Int.castRingHom (ZMod (p^(m-v)))) (g.eval ((y+p^(m-v) : ℕ) : ℤ))) =
      ZMod.stdAddChar ((Int.castRingHom (ZMod (p^(m-v)))) (g.eval (y : ℤ)))
    rw [← Polynomial.eval_natCast_map,← Polynomial.eval_natCast_map]
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
  have he : p^m=p^v*p^(m-v) := by rw [← pow_add,Nat.add_sub_of_le hv]
  rw [he,periodic_sum_full_blocks hper,← integerPolynomialSum_eq_range]

theorem integerPolynomialSum_content_constant {p : ℕ} [Fact p.Prime]
    (m v : ℕ) (hm : m ≤ v) (g : Polynomial ℤ) :
    integerPolynomialSum (p^m) (C ((p : ℤ)^v)*g)=((p^m : ℕ) : ℂ) := by
  rw [integerPolynomialSum_eq_range]
  have hz : (((p : ℤ)^v : ℤ) : ZMod (p^m))=0 := by
    rw [Int.cast_pow,Int.cast_natCast,← Nat.cast_pow,ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p hm
  simp [Polynomial.eval_mul,Polynomial.eval_C,Int.cast_mul,hz,AddChar.map_zero_eq_one]

/-- A nonconstant integer phase always admits a primitive normalization
of its nonconstant coefficients; its arbitrary constant phase is separate. -/
theorem exists_nonconstantPrimitive_factor {p : ℕ} [Fact p.Prime]
    (f : Polynomial ℤ) (hf : 0 < f.natDegree) :
    ∃ v : ℕ,∃ g : Polynomial ℤ,
      f=C ((p : ℤ)^v)*g+C (f.eval 0) ∧
      NonconstantPrimitiveAt p g ∧ g.natDegree ≤ f.natDegree := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨v,g,he,hg⟩ := exists_primitiveAt_factor (p := p)
    (shiftedDifference f 1 0) (shiftedDifference_ne_zero hf (by norm_num) 0)
  have he' : f-C (f.eval 0)=C ((p : ℤ)^v)*g := by
    simpa only [shiftedDifference,Polynomial.C_1,one_mul,Polynomial.C_0,add_zero,
      Polynomial.comp_X] using he
  have hg0 : g.coeff 0=0 := by
    have hh := congrArg (fun F : Polynomial ℤ => F.coeff 0) he
    change (shiftedDifference f 1 0).coeff 0=(C ((p : ℤ)^v)*g).coeff 0 at hh
    rw [shiftedDifference_coeff_zero,Polynomial.coeff_C_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hp)
  have hgprim : NonconstantPrimitiveAt p g := by
    obtain ⟨i,hi⟩ := hg
    refine ⟨i,?_,hi⟩
    by_contra hh
    have hi0 : i=0 := by omega
    exact hi (by simp [hi0,hg0])
  have hdeg : g.natDegree ≤ f.natDegree := by
    have hd := shiftedDifference_natDegree_le f 1 0
    rw [he,Polynomial.natDegree_C_mul (pow_ne_zero _ hp)] at hd
    exact hd
  exact ⟨v,g,sub_eq_iff_eq_add.mp he',hgprim,hdeg⟩

/-- The exact content loss at a prime power is its truncated valuation. -/
theorem polynomial_primepower_content_bound {p D : ℕ} [Fact p.Prime]
    (m v : ℕ) (g : Polynomial ℤ) (hg : NonconstantPrimitiveAt p g)
    (hgD : g.natDegree ≤ D) (a : ℤ) :
    ‖integerPolynomialSum (p^m) (C ((p : ℤ)^v)*g+C a)‖ ≤
      completeSumConstant D*((p^m : ℕ) : ℝ)^(1-1/(D : ℝ))*
        ((p^(min v m) : ℕ) : ℝ)^(1/(D : ℝ)) := by
  have hD : 1 ≤ D := (nonconstantPrimitiveAt_natDegree_pos hg).trans_le hgD
  have hC := completeSumConstant_ge_one hD
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_integerPolynomialSum_add_C]
  by_cases hmv : m ≤ v
  · rw [integerPolynomialSum_content_constant m v hmv,Complex.norm_natCast,min_eq_right hmv]
    have hq : 0 < ((p^m : ℕ) : ℝ) := by
      simpa only [Nat.cast_pow] using pow_pos hp m
    have he : ((p^m : ℕ) : ℝ)^(1-1/(D : ℝ))*((p^m : ℕ) : ℝ)^(1/(D : ℝ))=
        ((p^m : ℕ) : ℝ) := by
      rw [← Real.rpow_add hq,show (1-1/(D : ℝ))+1/(D : ℝ)=1 by ring,Real.rpow_one]
    rw [mul_assoc,he]
    exact le_mul_of_one_le_left hq.le hC
  · have hvm : v ≤ m := by omega
    rw [integerPolynomialSum_content_reduced m v hvm,norm_mul,Complex.norm_natCast,min_eq_left hvm]
    have hb := primitive_polynomial_primepower_bound (m-v) g hg hgD
    apply (mul_le_mul_of_nonneg_left hb (show (0 : ℝ)≤(p^v : ℕ) by positivity)).trans
    apply le_of_eq
    have hmvcast : ((m-v : ℕ) : ℝ)=(m : ℝ)-(v : ℝ) := Nat.cast_sub hvm
    simp only [Nat.cast_pow]
    simp_rw [← Real.rpow_natCast (p : ℝ)]
    simp_rw [← Real.rpow_mul hp.le]
    calc
      _ = completeSumConstant D*(p : ℝ)^((v : ℝ)+
          ((m-v : ℕ) : ℝ)*(1-1/(D : ℝ))) := by
        rw [Real.rpow_add hp]
        ring
      _ = completeSumConstant D*(p : ℝ)^((m : ℝ)*(1-1/(D : ℝ))+
          (v : ℝ)*(1/(D : ℝ))) := by
        congr 2
        rw [hmvcast]
        ring
      _ = _ := by rw [Real.rpow_add hp]; ring

#print axioms exists_nonconstantPrimitive_factor
#print axioms polynomial_primepower_content_bound
end Waring.PolicyCompletionPolynomialContentSum
