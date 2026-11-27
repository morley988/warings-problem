import WaringSiegel.WSL4MajorRamanujamBinomial
import WaringSiegel.WSL4RamanujamCoefficientRing
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! # Rational prime-integral inverses for the exact binomial unit factor -/
noncomputable section
open IsLocalRing Polynomial
namespace WaringSiegel.WSL4
open WSL4Local

variable {A : Type*} [CommRing A]

theorem nat_unit_inverse_mem_rationalPrimeCoefficientRing
    (p n : ℕ) (hp : p.Prime) (hn : ¬p ∣ n)
    (u : Aˣ) (hu : (u:A)=(n:A)) :
    ((u⁻¹:Aˣ):A)∈rationalPrimeCoefficientRing p A := by
  refine ⟨1,(n:ℤ),?_,?_⟩
  · exact ((hp.coprime_iff_not_dvd.mpr hn).symm).isCoprime
  · simp only [Int.cast_natCast,Int.cast_one,← hu]
    simp

theorem prime_power_choose_normalizing_unit
    [IsLocalRing A] (p r k : ℕ) (hp : p.Prime) (hkr : k ≤ r)
    [CharP (ResidueField A) p] :
    ∃ v : Aˣ,
      (v:A)∈rationalPrimeCoefficientRing p A ∧
      (v:A)*((p^r).choose (p^k):A)=(p:A)^(r-k) := by
  obtain ⟨n,he,hu,hn⟩ := prime_power_choose_local_unit (A:=A) p r k hp hkr
  obtain ⟨u,hu⟩ := hu
  refine ⟨u⁻¹,nat_unit_inverse_mem_rationalPrimeCoefficientRing p n hp hn u hu,?_⟩
  rw [he,Nat.cast_mul,Nat.cast_pow,← hu]
  calc
    ((u⁻¹:Aˣ):A)*((p:A)^(r-k)*(u:A)) =
      (p:A)^(r-k)*(((u⁻¹:Aˣ):A)*(u:A)) := by ring
    _ = _ := by simp

/-- Multiplication by the binomial-unit reciprocal preserves integral coefficient
membership and the literal degree bound of every coefficient polynomial. -/
theorem normalized_integer_polynomial_coefficients
    (p : ℕ) (v : A) (hv : v∈rationalPrimeCoefficientRing p A) (Q : ℤ[X]) :
    (∀ i,(C v*Q.map (Int.castRingHom A)).coeff i∈rationalPrimeCoefficientRing p A) ∧
      (C v*Q.map (Int.castRingHom A)).natDegree ≤ Q.natDegree := by
  constructor
  · intro i
    rw [coeff_C_mul,coeff_map]
    exact (rationalPrimeCoefficientRing p A).mul_mem hv
      (mem_rationalPrimeCoefficientRing_intCast p (Q.coeff i))
  · exact (natDegree_C_mul_le _ _).trans natDegree_map_le

#print axioms nat_unit_inverse_mem_rationalPrimeCoefficientRing
#print axioms prime_power_choose_normalizing_unit
#print axioms normalized_integer_polynomial_coefficients
end WaringSiegel.WSL4
