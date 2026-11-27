import WaringSiegel.WSL4WeilJolyReduction

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000

/-- The integer polynomial S/k has affine reduction, with slope exactly one. -/
theorem exists_joly_integral_polynomial (k : ℕ) [Fact k.Prime] (hk : 2<k) :
    ∃ F : ℤ[X], ∃ c : ZMod k,
      jolyNumerator k=C (k:ℤ)*F ∧
      F.map (Int.castRingHom (ZMod k))=X+C c := by
  obtain ⟨F,hF⟩ := jolyNumerator_dvd k hk
  have hk0 : (k:ℤ)≠0 := by exact_mod_cast (Fact.out : k.Prime).ne_zero
  have hd : F.degree<k := by
    rw [← degree_C_mul hk0,← hF]
    exact jolyNumerator_degree_lt k
  have hdn : F.natDegree<k := by
    by_cases hF0 : F=0
    · simp [hF0,(Fact.out : k.Prime).pos]
    · exact (natDegree_lt_iff_degree_lt hF0).mpr hd
  have hder : F.derivative=jolyDerivative k := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hk0)
    have h := congrArg derivative hF
    rw [jolyNumerator_derivative,derivative_C_mul] at h
    exact h.symm
  have hmapder : (F.map (Int.castRingHom (ZMod k))).derivative=1 := by
    rw [derivative_map,hder,jolyDerivative_map_eq_one]
  refine ⟨F,(F.map (Int.castRingHom (ZMod k))).coeff 0,hF,?_⟩
  exact primePolynomial_affine_of_derivative_one k _
    (natDegree_map_le.trans_lt hdn) hmapder
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_joly_integral_polynomial
