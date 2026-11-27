import Waring.PolicyCompletionPolynomialBranch
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.RingDivision

/-! # Prime content and actual derivative multiplicities

Every nonzero integer polynomial has an exact prime-power content factor.
For a polynomial with a unit nonconstant coefficient, the content of its
derivative is bounded by its degree. The root multiplicity identifies the
unit Taylor coefficient used by the already proved branch degree drop.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialContent
open Polynomial PolicyCompletionPolynomialBranch

def PrimitiveAt (p : ℕ) (f : Polynomial ℤ) : Prop :=
  ∃ i : ℕ,¬(p : ℤ) ∣ f.coeff i

def NonconstantPrimitiveAt (p : ℕ) (f : Polynomial ℤ) : Prop :=
  ∃ i : ℕ,0 < i ∧ ¬(p : ℤ) ∣ f.coeff i

theorem primitiveAt_map_ne_zero {p : ℕ} {f : Polynomial ℤ} (hf : PrimitiveAt p f) :
    f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  obtain ⟨i,hi⟩ := hf
  intro he
  have hc := congrArg (fun F : Polynomial (ZMod p) => F.coeff i) he
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at hc
  exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc)

/-- Exact removal of the maximal common power of p, with a genuinely
primitive remaining polynomial. -/
theorem exists_primitiveAt_factor {p : ℕ} [Fact p.Prime]
    (f : Polynomial ℤ) (hf : f ≠ 0) :
    ∃ t : ℕ,∃ g : Polynomial ℤ,f=C ((p : ℤ)^t)*g ∧ PrimitiveAt p g := by
  classical
  have hlc : f.coeff f.natDegree ≠ 0 := by simpa only [coeff_natDegree] using
    (Polynomial.leadingCoeff_ne_zero.mpr hf)
  have hex : ∃ n : ℕ,¬C ((p : ℤ)^n) ∣ f := by
    refine ⟨padicValInt p (f.coeff f.natDegree)+1,?_⟩
    intro hd
    have hd' := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hd f.natDegree
    have hh := (padicValInt_dvd_iff _ _).mp hd'
    exact hh.elim hlc (by omega)
  let n := Nat.find hex
  have hn : ¬C ((p : ℤ)^n) ∣ f := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n=0 := by omega
    exact hn (by simp [hn0])
  have hdiv : C ((p : ℤ)^(n-1)) ∣ f := by
    by_contra hd
    exact (Nat.find_min hex (show n-1 < n by omega)) hd
  obtain ⟨g,hg⟩ := hdiv
  refine ⟨n-1,g,hg,?_⟩
  by_contra hprim
  have hgdiv : C (p : ℤ) ∣ g := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    by_contra hi
    exact hprim ⟨i,hi⟩
  obtain ⟨u,hu⟩ := hgdiv
  apply hn
  refine ⟨u,?_⟩
  rw [hg,hu,← mul_assoc,← Polynomial.C_mul,← pow_succ,Nat.sub_add_cancel hnpos]

/-- A unit nonconstant coefficient forces p^t<=degree when p^t divides
all derivative coefficients. This controls every exceptional small prime. -/
theorem derivative_content_pow_le_degree {p : ℕ} [Fact p.Prime]
    (f D : Polynomial ℤ) (t : ℕ) (hf : NonconstantPrimitiveAt p f)
    (hder : f.derivative=C ((p : ℤ)^t)*D) : p^t ≤ f.natDegree := by
  obtain ⟨i,hi,hcoeff⟩ := hf
  have hci : f.coeff i ≠ 0 := by intro he; exact hcoeff (he ▸ dvd_zero _)
  have hii : (i : ℤ) ≠ 0 := by exact_mod_cast hi.ne'
  have hd : (p : ℤ)^t ∣ f.coeff i*(i : ℤ) := by
    have hh := congrArg (fun F : Polynomial ℤ => F.coeff (i-1)) hder
    simp only [Polynomial.coeff_derivative,Polynomial.coeff_C_mul,Nat.sub_add_cancel hi] at hh
    have hiCast : ((i-1 : ℕ) : ℤ)+1=(i : ℤ) := by
      exact_mod_cast Nat.sub_add_cancel hi
    rw [hiCast] at hh
    rw [hh]
    exact dvd_mul_right _ _
  have hv : t ≤ padicValInt p (i : ℤ) := by
    have hh := (padicValInt_dvd_iff t (f.coeff i*(i : ℤ))).mp hd
    rcases hh with hh | hh
    · exact False.elim ((mul_ne_zero hci hii) hh)
    · rw [padicValInt.mul hci hii,padicValInt.eq_zero_of_not_dvd hcoeff,zero_add] at hh
      exact hh
  have hdi : (p : ℤ)^t ∣ (i : ℤ) := (padicValInt_dvd_iff _ _).mpr (Or.inr hv)
  have hdnat : p^t ∣ i := by exact_mod_cast hdi
  exact (Nat.le_of_dvd hi hdnat).trans (Polynomial.le_natDegree_of_ne_zero hci)

theorem reduced_rootMultiplicity_taylor_unit {p : ℕ} [Fact p.Prime]
    (D : Polynomial ℤ) (hD : PrimitiveAt p D) (r : ℤ) :
    ¬(p : ℤ) ∣ (taylor r D).coeff
      ((D.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)) := by
  let c : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let E := D.map c
  have hE : E ≠ 0 := primitiveAt_map_ne_zero hD
  have hmap : (taylor r D).map c=taylor (r : ZMod p) E := by
    simp only [taylor_apply,Polynomial.map_comp,Polynomial.map_add,
      Polynomial.map_X,Polynomial.map_C,E]
    rfl
  have ht : taylor (r : ZMod p) E ≠ 0 := by
    exact (Polynomial.taylor_eq_zero _ _).not.mpr hE
  have hunit : (taylor (r : ZMod p) E).coeff (E.rootMultiplicity (r : ZMod p)) ≠ 0 := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr ht
  intro hdiv
  have hzero : (((taylor r D).coeff (E.rootMultiplicity (r : ZMod p)) : ℤ) : ZMod p)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
  apply hunit
  rw [← hmap,Polynomial.coeff_map]
  exact hzero

theorem sum_rootMultiplicity_le_degree {p : ℕ} [Fact p.Prime]
    (D : Polynomial (ZMod p)) :
    (∑ r ∈ D.roots.toFinset,D.rootMultiplicity r) ≤ D.natDegree := by
  classical
  simp_rw [← Polynomial.count_roots]
  rw [Multiset.toFinset_sum_count_eq]
  exact Polynomial.card_roots' _

#print axioms exists_primitiveAt_factor
#print axioms derivative_content_pow_le_degree
#print axioms reduced_rootMultiplicity_taylor_unit
end Waring.PolicyCompletionPolynomialContent
