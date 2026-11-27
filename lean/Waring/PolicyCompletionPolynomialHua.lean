import Waring.PolicyCompletionPolynomialHuaBounds

/-! # A proved prime-power Hua bound for arbitrary integer polynomials

The proof combines the actual prime-field Mordell estimate with exact
stationary filtering and Taylor branch recursion. Derivative content is
retained through every branch; root multiplicities control the sum of the
constants. Small primes are included by the bounded derivative content.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialHua
open Polynomial PolicyCompletionPolynomialRecursion PolicyCompletionPolynomialContent
  PolicyCompletionPolynomialResidues PolicyCompletionPolynomialPrime
  PolicyCompletionPolynomialHuaBounds PolicyCompletionPolynomialBranch

theorem prime_level_bound {p D : ℕ} [Fact p.Prime]
    (f F : Polynomial ℤ) (t : ℕ) (hf : NonconstantPrimitiveAt p f)
    (hfD : f.natDegree ≤ D) (hder : f.derivative=C ((p : ℤ)^t)*F)
    (hDp : D < p) :
    ‖integerPolynomialSum p f‖ ≤
      (huaConstant D)^((F.map (Int.castRingHom (ZMod p))).natDegree+1)*
        (p : ℝ)^(huaExponent 1 t (F.map (Int.castRingHom (ZMod p))).natDegree) := by
  have ht := good_prime_content_eq_zero f F t hf hder hfD hDp
  subst t
  let E := f.map (Int.castRingHom (ZMod p))
  have hE : 0 < E.natDegree := nonconstantPrimitiveAt_map_natDegree_pos hf
  have hED : E.natDegree ≤ D := Polynomial.natDegree_map_le.trans hfD
  have hdiff : E.derivative=F.map (Int.castRingHom (ZMod p)) := by
    simp only [E,Polynomial.derivative_map,hder,pow_zero,Polynomial.C_1,one_mul]
  have he : (F.map (Int.castRingHom (ZMod p))).natDegree+1=E.natDegree := by
    rw [← hdiff]
    exact derivative_natDegree_add_one E hE (hED.trans_lt hDp)
  have hb := prime_polynomial_bound_fixed_degree E hE hED hDp
  have hK := huaConstant_ge_two D
  have hKK : huaConstant D ≤ (huaConstant D)^(E.natDegree) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ huaConstant D) hE
  have hden : ((F.map (Int.castRingHom (ZMod p))).natDegree : ℝ)+1=(E.natDegree : ℝ) := by
    exact_mod_cast he
  change ‖FiniteFieldMordell.polynomialSum p E‖ ≤ _
  unfold huaExponent
  simp only [Nat.cast_one,Nat.cast_zero,sub_zero,hden]
  rw [he]
  exact hb.trans (mul_le_mul_of_nonneg_right hKK (by positivity))

/-- Uniform prime-power cancellation with exact derivative content and
its reduced degree. This stronger invariant is stable under every branch. -/
theorem integerPolynomialSum_hua_internal {p D : ℕ} [Fact p.Prime]
    (m : ℕ) (f F : Polynomial ℤ) (t : ℕ) (hf : NonconstantPrimitiveAt p f)
    (hfD : f.natDegree ≤ D) (hder : f.derivative=C ((p : ℤ)^t)*F)
    (hF : PrimitiveAt p F) :
    ‖integerPolynomialSum (p^m) f‖ ≤
      (huaConstant D)^((F.map (Int.castRingHom (ZMod p))).natDegree+1)*
        (p : ℝ)^(huaExponent m t (F.map (Int.castRingHom (ZMod p))).natDegree) := by
  induction m using Nat.strong_induction_on generalizing f F t with
  | h m ih =>
      let K := huaConstant D
      let e := (F.map (Int.castRingHom (ZMod p))).natDegree
      have hK : 2 ≤ K := huaConstant_ge_two D
      have hK1 : 1 ≤ K := by linarith
      have hp : 0 < p := (Fact.out : p.Prime).pos
      have hpr : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
      have hpp : 0 < (p : ℝ) := zero_lt_one.trans_le hpr
      have hpInt : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
      change ‖integerPolynomialSum (p^m) f‖ ≤ K^(e+1)*(p : ℝ)^(huaExponent m t e)
      by_cases hm0 : m=0
      · subst m
        have hb : ‖integerPolynomialSum 1 f‖ ≤ (1 : ℝ) := by
          simpa only [Nat.cast_one] using norm_integerPolynomialSum_le 1 f
        have he : 0 ≤ huaExponent 0 t e := by
          unfold huaExponent
          simp only [Nat.cast_zero,zero_sub,neg_div,neg_neg]
          positivity
        have hkp : 1 ≤ K^(e+1) := one_le_pow₀ hK1
        have hppow : 1 ≤ (p : ℝ)^(huaExponent 0 t e) := Real.one_le_rpow hpr he
        simpa only [pow_zero,Nat.cast_one] using hb.trans (one_le_mul_of_one_le_of_one_le hkp hppow)
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      by_cases hm : m ≤ 2*t+1
      · by_cases hpD : p ≤ D
        · have hpt := (derivative_content_pow_le_degree f F t hf hder).trans hfD
          exact (norm_integerPolynomialSum_le (p^m) f).trans (by
            simpa only [Nat.cast_pow] using small_prime_trivial_bound (e := e)
              (show 1 ≤ p by omega) hpD hpt hm)
        · have hDp : D < p := lt_of_not_ge hpD
          have ht := good_prime_content_eq_zero f F t hf hder hfD hDp
          have hmEq : m=1 := by omega
          subst m
          simpa only [pow_one] using prime_level_bound f F t hf hfD hder hDp
      have hmdeep : 2*t+2 ≤ m := by omega
      have hcritical := integerPolynomialSum_eq_critical_residues m t hmdeep f F hder
      change integerPolynomialSum (p^m) f=
        ∑ r ∈ criticalResidues p F,residuePolynomialSum p m r f at hcritical
      have hsum := criticalMultiplicity_sum_le (p := p) F
      change (∑ r ∈ criticalResidues p F,criticalMultiplicity p F r) ≤ e at hsum
      have hνpos : ∀ r ∈ criticalResidues p F,1 ≤ criticalMultiplicity p F r :=
        fun r hr => criticalMultiplicity_pos F hF hr
      have hlocal (r : ℕ) (hr : r ∈ criticalResidues p F) :
          ‖residuePolynomialSum p m r f‖ ≤
            K^(criticalMultiplicity p F r+1)*(p : ℝ)^(huaExponent m t e) := by
        let ν := criticalMultiplicity p F r
        have hν : 1 ≤ ν := hνpos r hr
        have hνe : ν ≤ e := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr).trans hsum
        obtain ⟨σ,hσ,g,hbranch,hg,hgdeg⟩ :=
          exists_normalized_branch (p := p) f (nonconstantPrimitiveAt_natDegree_pos hf) r
        obtain ⟨τ,G,hnew,hG⟩ := exists_primitiveAt_factor (p := p) g.derivative
          (nonconstantPrimitiveAt_derivative_ne_zero hg)
        have hunit : ¬(p : ℤ) ∣ (taylor (r : ℤ) F).coeff ν := by
          simpa only [ν,criticalMultiplicity,Int.cast_natCast] using
            reduced_rootMultiplicity_taylor_unit F hF r
        have hcontent := branch_content_le f F g G hpInt t σ τ ν hder hbranch hnew hunit
        have hnewdeg := branch_reduced_derivative_degree_le f F g G hp r
          t σ τ ν hder hbranch hnew hunit
        have hbranchBound : ‖residuePolynomialSum p m r f‖ ≤ K^(ν+1)*(p : ℝ)^(huaExponent m t ν) := by
          by_cases hsmall : m ≤ σ+τ
          · have hfrac : ((m : ℝ)-(t : ℝ))/((ν : ℝ)+1) ≤ 1 := by
              apply (div_le_iff₀ (by positivity : (0 : ℝ)<(ν : ℝ)+1)).mpr
              have hc : (σ : ℝ)+(τ : ℝ) ≤ (t : ℝ)+1+(ν : ℝ) := by exact_mod_cast hcontent
              have hs : (m : ℝ) ≤ (σ : ℝ)+(τ : ℝ) := by exact_mod_cast hsmall
              linarith
            have he : ((m-1 : ℕ) : ℝ) ≤ huaExponent m t ν := by
              rw [Nat.cast_sub hm1,Nat.cast_one]
              unfold huaExponent
              linarith
            calc
              _ ≤ (p : ℝ)^(m-1) := norm_residuePolynomialSum_le m r f
              _ ≤ (p : ℝ)^(huaExponent m t ν) := by
                rw [← Real.rpow_natCast]
                exact Real.rpow_le_rpow_of_exponent_le hpr he
              _ ≤ _ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hK1)
          · have hσm : σ ≤ m := by omega
            have hnext : m-σ < m := by omega
            have htau : τ ≤ m-σ := by omega
            have hIH := ih (m-σ) hnext g G τ hg (hgdeg.trans hfD) hnew hG
            have hnorm : ‖residuePolynomialSum p m r f‖=
                (p : ℝ)^(σ-1)*‖integerPolynomialSum (p^(m-σ)) g‖ := by
              rw [residuePolynomialSum_eq_reduced m σ r hσ hσm f g hbranch,
                norm_mul,norm_mul]
              simp [ZMod.stdAddChar_apply]
            have hcoef : K^((G.map (Int.castRingHom (ZMod p))).natDegree+1) ≤ K^(ν+1) :=
              pow_le_pow_right₀ hK1 (Nat.add_le_add_right hnewdeg 1)
            have hexp := branch_exponent_le hσm hσ hcontent hnewdeg htau
            calc
              _ = (p : ℝ)^(σ-1)*‖integerPolynomialSum (p^(m-σ)) g‖ := hnorm
              _ ≤ (p : ℝ)^(σ-1)*(K^((G.map (Int.castRingHom (ZMod p))).natDegree+1)*
                  (p : ℝ)^(huaExponent (m-σ) τ (G.map (Int.castRingHom (ZMod p))).natDegree)) :=
                mul_le_mul_of_nonneg_left hIH (by positivity)
              _ ≤ (p : ℝ)^(σ-1)*(K^(ν+1)*
                  (p : ℝ)^(huaExponent (m-σ) τ (G.map (Int.castRingHom (ZMod p))).natDegree)) := by
                gcongr
              _ = K^(ν+1)*(p : ℝ)^(((σ-1 : ℕ) : ℝ)+
                  huaExponent (m-σ) τ (G.map (Int.castRingHom (ZMod p))).natDegree) := by
                rw [Real.rpow_add hpp,Real.rpow_natCast]
                ring
              _ ≤ _ := mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hpr hexp) (pow_nonneg (by linarith) _)
        have hmtn : 0 ≤ (m : ℝ)-(t : ℝ) := by
          have hh : (t : ℝ) ≤ m := by exact_mod_cast (show t ≤ m by omega)
          linarith
        have hdiv : ((m : ℝ)-(t : ℝ))/((e : ℝ)+1) ≤
            ((m : ℝ)-(t : ℝ))/((ν : ℝ)+1) :=
          div_le_div_of_nonneg_left hmtn (by positivity)
            (by exact_mod_cast Nat.add_le_add_right hνe 1)
        have hexp : huaExponent m t ν ≤ huaExponent m t e := by unfold huaExponent; linarith
        exact hbranchBound.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hpr hexp) (pow_nonneg (by linarith) _))
      rw [hcritical]
      calc
        _ ≤ ∑ r ∈ criticalResidues p F,‖residuePolynomialSum p m r f‖ := norm_sum_le _ _
        _ ≤ ∑ r ∈ criticalResidues p F,K^(criticalMultiplicity p F r+1)*(p : ℝ)^(huaExponent m t e) :=
          Finset.sum_le_sum hlocal
        _ = (∑ r ∈ criticalResidues p F,K^(criticalMultiplicity p F r+1))*(p : ℝ)^(huaExponent m t e) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (sum_branch_constants_le _ _ hK hνpos hsum) (by positivity)

#print axioms integerPolynomialSum_hua_internal
end Waring.PolicyCompletionPolynomialHua
