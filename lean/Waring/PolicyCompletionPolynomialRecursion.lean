import Waring.PolicyCompletionPolynomialResidues

/-! # Actual polynomial branches and the critical-point decomposition -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialRecursion
open Polynomial EndgameCompletion PolicyCompletionPolynomialStationary
  PolicyCompletionPolynomialBranch PolicyCompletionPolynomialContent
  PolicyCompletionPolynomialResidues

theorem nonconstantPrimitiveAt_natDegree_pos {p : ℕ} {f : Polynomial ℤ}
    (hf : NonconstantPrimitiveAt p f) : 0 < f.natDegree := by
  obtain ⟨i,hi,hci⟩ := hf
  have hne : f.coeff i ≠ 0 := by intro he; exact hci (he ▸ dvd_zero _)
  exact hi.trans_le (Polynomial.le_natDegree_of_ne_zero hne)

theorem nonconstantPrimitiveAt_derivative_ne_zero {p : ℕ} {f : Polynomial ℤ}
    (hf : NonconstantPrimitiveAt p f) : f.derivative ≠ 0 := by
  intro he
  have hd := Polynomial.natDegree_eq_zero_of_derivative_eq_zero he
  exact (nonconstantPrimitiveAt_natDegree_pos hf).ne' hd

theorem shiftedDifference_coeff_zero (f : Polynomial ℤ) (p r : ℤ) :
    (shiftedDifference f p r).coeff 0=0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [shiftedDifference]

theorem shiftedDifference_natDegree_le (f : Polynomial ℤ) (p r : ℤ) :
    (shiftedDifference f p r).natDegree ≤ f.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hj0 : j ≠ 0 := by omega
  rw [shiftedDifference,Polynomial.coeff_sub,affine_comp_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hj)]
  simp only [Polynomial.coeff_C,if_neg hj0,zero_mul,sub_self]

theorem shiftedDifference_ne_zero {f : Polynomial ℤ} (hf : 0 < f.natDegree)
    {p : ℤ} (hp : p ≠ 0) (r : ℤ) : shiftedDifference f p r ≠ 0 := by
  have hfn : f ≠ 0 := by intro he; simp [he] at hf
  have hc : (shiftedDifference f p r).coeff f.natDegree ≠ 0 := by
    rw [shiftedDifference,Polynomial.coeff_sub,affine_comp_coeff,
      Polynomial.coeff_taylor_natDegree]
    simp only [Polynomial.coeff_C,if_neg hf.ne',sub_zero]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hfn) (pow_ne_zero _ hp)
  intro he
  exact hc (by simp [he])

/-- Every actual branch has positive removable content and a nonconstant
primitive normalized phase of no larger degree. -/
theorem exists_normalized_branch {p : ℕ} [Fact p.Prime]
    (f : Polynomial ℤ) (hf : 0 < f.natDegree) (r : ℤ) :
    ∃ σ : ℕ,1 ≤ σ ∧ ∃ g : Polynomial ℤ,
      shiftedDifference f (p : ℤ) r=C ((p : ℤ)^σ)*g ∧
      NonconstantPrimitiveAt p g ∧ g.natDegree ≤ f.natDegree := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨σ,g,he,hg⟩ := exists_primitiveAt_factor (p := p)
    (shiftedDifference f (p : ℤ) r) (shiftedDifference_ne_zero hf hp r)
  have hg0 : g.coeff 0=0 := by
    have hh := congrArg (fun F : Polynomial ℤ => F.coeff 0) he
    change (shiftedDifference f (p : ℤ) r).coeff 0=(C ((p : ℤ)^σ)*g).coeff 0 at hh
    rw [shiftedDifference_coeff_zero,Polynomial.coeff_C_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hp)
  have hσ : 1 ≤ σ := by
    by_contra h
    have hσ0 : σ=0 := by omega
    have hg' : shiftedDifference f (p : ℤ) r=g := by simpa [hσ0] using he
    obtain ⟨i,hi⟩ := hg
    apply hi
    rw [← hg']
    by_cases hi0 : i=0
    · simp [hi0,shiftedDifference_coeff_zero]
    · rw [shiftedDifference,Polynomial.coeff_sub,affine_comp_coeff]
      simp only [Polynomial.coeff_C,if_neg hi0,sub_zero]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ hi0) _
  have hgprim : NonconstantPrimitiveAt p g := by
    obtain ⟨i,hi⟩ := hg
    refine ⟨i,?_,hi⟩
    by_contra h
    have hi0 : i=0 := by omega
    exact hi (by simp [hi0,hg0])
  have hdeg : g.natDegree ≤ f.natDegree := by
    have hd := shiftedDifference_natDegree_le f (p : ℤ) r
    rw [he,Polynomial.natDegree_C_mul (pow_ne_zero _ hp)] at hd
    exact hd
  exact ⟨σ,hσ,g,he,hgprim,hdeg⟩

theorem primepower_eval_filter_iff {p : ℕ} [Fact p.Prime]
    (m : ℕ) (hm : 1 ≤ m) (D : Polynomial ℤ) (x : ZMod (p^m)) (r : ℕ)
    (hr : x.val%p=r) :
    p ∣ ((D.map (Int.castRingHom (ZMod (p^m)))).eval x).val ↔
      (D.map (Int.castRingHom (ZMod p))).eval (r : ZMod p)=0 := by
  let π : ZMod (p^m) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by omega : m ≠ 0)) (ZMod p)
  have he : (D.map (Int.castRingHom (ZMod (p^m)))).eval x=
      ((D.eval (x.val : ℤ) : ℤ) : ZMod (p^m)) := by
    nth_rw 1 [← ZMod.natCast_zmod_val x]
    rw [Polynomial.eval_natCast_map]
    rfl
  have hπ (a : ZMod (p^m)) : π a=(a.val : ZMod p) := castHom_primepower_eq_val m hm a
  rw [← ZMod.natCast_eq_zero_iff,← hπ,he]
  simp only [map_intCast]
  have hxr : (x.val : ZMod p)=(r : ZMod p) := by
    rw [← ZMod.natCast_mod x.val p,hr]
  change (Int.castRingHom (ZMod p)) (D.eval (x.val : ℤ))=0 ↔ _
  rw [← Polynomial.eval_natCast_map (Int.castRingHom (ZMod p)) D x.val,hxr]

/-- The exact complete sum only contains the critical residue branches
of the primitive derivative. -/
theorem integerPolynomialSum_eq_critical_residues {p : ℕ} [Fact p.Prime]
    (m t : ℕ) (hm : 2*t+2 ≤ m) (f D : Polynomial ℤ)
    (hder : f.derivative=C ((p : ℤ)^t)*D) :
    integerPolynomialSum (p^m) f=
      ∑ r ∈ (Finset.range p).filter
        (fun r : ℕ => (D.map (Int.castRingHom (ZMod p))).eval (r : ZMod p)=0),
        residuePolynomialSum p m r f := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let S : Finset (ZMod (p^m)) := Finset.univ.filter
    (fun x => p ∣ ((D.map (Int.castRingHom (ZMod (p^m)))).eval x).val)
  have hmap : ∀ x ∈ S,x.val%p ∈ Finset.range p := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  unfold integerPolynomialSum
  rw [completePolynomialSum_primitiveDerivative_filter m t hm f D hder]
  change (∑ x ∈ S,ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod (p^m)))).eval x)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hcrit : (D.map (Int.castRingHom (ZMod p))).eval (r : ZMod p)=0
  · rw [if_pos hcrit]
    have he : S.filter (fun x => x.val%p=r)=
        Finset.univ.filter (fun x : ZMod (p^m) => x.val%p=r) := by
      ext x
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · exact fun h => h.2
      · intro hx
        exact ⟨(primepower_eval_filter_iff m (by omega) D x r hx).mpr hcrit,hx⟩
    rw [he,sum_zmod_filter_residue (p^m) p (p^(m-1)) r hp
      (by rw [← pow_succ',Nat.sub_add_cancel (show 1 ≤ m by omega)]) (Finset.mem_range.mp hr)]
    unfold residuePolynomialSum
    apply Finset.sum_congr rfl
    intro y hy
    rw [Polynomial.eval_natCast_map]
    congr 1
  · rw [if_neg hcrit]
    have he : S.filter (fun x => x.val%p=r)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx,hxr⟩ := Finset.mem_filter.mp hx
      have hd := (Finset.mem_filter.mp hx).2
      exact hcrit ((primepower_eval_filter_iff m (by omega) D x r hxr).mp hd)
    rw [he,Finset.sum_empty]

#print axioms exists_normalized_branch
#print axioms integerPolynomialSum_eq_critical_residues
end Waring.PolicyCompletionPolynomialRecursion
