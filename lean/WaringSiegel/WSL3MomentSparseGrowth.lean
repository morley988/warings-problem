import WaringSiegel.WSL3MomentSparseModular
import WaringSiegel.WSL2UnitLogGrowth

/-!
# Epsilon bookkeeping for the sparse residue partition

The spacing depth is ceil(tau*r*H)+1.  The number of annuli contributes
only a fixed polynomial in H, and the p^c residue count costs an arbitrarily
small power after tau is chosen. Every factor in the modular estimate is
absorbed in a single epsilon loss in p^H.
-/

noncomputable section
open GafniTao
open scoped BigOperators Classical

namespace WaringSiegel.WSL3
open WSL2

theorem exists_one_add_nat_pow_le_primePower_rpow (p n : ℕ) (hp : 1 < p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ,
      (1+(H : ℝ))^n ≤ C*((p : ℝ)^H)^ε := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  let A := 1+(Real.log (p : ℝ))⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; linarith [inv_pos.mpr hlog]
  obtain ⟨B,hB,hbound⟩ := exists_one_add_log_pow_le_rpow n hε
  refine ⟨A^n*B,by positivity,?_⟩
  intro H
  have hbase : 1+(H : ℝ) ≤ A*(1+Real.log ((p : ℝ)^H)) := by
    rw [Real.log_pow]
    calc
      1+(H : ℝ) ≤ A+(H : ℝ)*(Real.log (p : ℝ)+1) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg H) hlog.le]
      _ = A*(1+(H : ℝ)*Real.log (p : ℝ)) := by
        dsimp [A]
        field_simp <;> ring
  calc
    _ ≤ (A*(1+Real.log ((p : ℝ)^H)))^n := pow_le_pow_left₀ (by positivity) hbase n
    _ = A^n*(1+Real.log ((p : ℝ)^H))^n := mul_pow _ _ _
    _ ≤ A^n*(B*((p : ℝ)^H)^ε) := by
      gcongr
      exact hbound _ (one_le_pow₀ hpR.le)
    _ = _ := by ring

/-- Choice of small native exponents together with a uniform explicit
bound for every annulus/residue partition loss. -/
theorem sparse_partition_epsilon_parameters (p r : ℕ) (hp : 1 < p) (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ δ D : ℝ, 0 < τ ∧ 0 < δ ∧ 0 < D ∧
      ∀ H : ℕ, ∃ c : ℕ, 1 ≤ c ∧ τ*(r*H : ℕ) ≤ (c : ℝ) ∧
        (1+(H : ℝ)*(p : ℝ)^c)^(2*wooleyTriangular r) * (p^(r*H) : ℝ)^δ ≤
          D*((p : ℝ)^H)^ε := by
  let n := 2*wooleyTriangular r
  have hn : 0 < n := by
    dsimp [n,wooleyTriangular]
    have : 2 ≤ r*(r+1) := by nlinarith
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let τ : ℝ := ε/(4*(r : ℝ)*n)
  let δ : ℝ := ε/(2*(r : ℝ))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A,hA,hpoly⟩ := exists_one_add_nat_pow_le_primePower_rpow p n hp
    (show 0 < ε/4 by linarith)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  let D : ℝ := A*(p : ℝ)^(2*n)
  refine ⟨τ,δ,D,hτ,hδ,by dsimp [D]; positivity,?_⟩
  intro H
  let c := Nat.ceil (τ*(r*H : ℕ)) + 1
  have hx0 : 0 ≤ τ*(r*H : ℕ) := by positivity
  have hcscale : τ*(r*H : ℕ) ≤ (c : ℝ) := by
    have h := Nat.le_ceil (τ*(r*H : ℕ))
    simp only [c,Nat.cast_add,Nat.cast_one]
    linarith
  have hcupper : (c : ℝ) ≤ τ*(r*H : ℕ)+2 := by
    have h := Nat.ceil_lt_add_one hx0
    simp only [c,Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨c,by dsimp [c]; omega,hcscale,?_⟩
  have hpC : 1 ≤ (p : ℝ)^c := one_le_pow₀ hpR.le
  have hN : 1+(H : ℝ)*(p : ℝ)^c ≤ (1+(H : ℝ))*(p : ℝ)^c := by nlinarith
  have hτeq : τ*(r : ℝ)*(n : ℝ)=ε/4 := by dsimp [τ]; field_simp
  have hδeq : (r : ℝ)*δ=ε/2 := by dsimp [δ]; field_simp
  have hres : ((p : ℝ)^c)^n ≤ (p : ℝ)^(2*n)*((p : ℝ)^H)^(ε/4) := by
    have hexp : ((c*n : ℕ) : ℝ) ≤ ((2*n : ℕ) : ℝ)+(H : ℝ)*(ε/4) := by
      push_cast at hcupper ⊢
      have hh := mul_le_mul_of_nonneg_right hcupper hnR.le
      nlinarith [hτeq]
    calc
      _ = (p : ℝ)^((c*n : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        exact (pow_mul (p : ℝ) c n).symm
      _ ≤ (p : ℝ)^(((2*n : ℕ) : ℝ)+(H : ℝ)*(ε/4)) :=
        Real.rpow_le_rpow_of_exponent_le hpR.le hexp
      _ = _ := by
        rw [Real.rpow_add (by linarith), Real.rpow_natCast,
          Real.rpow_mul (by linarith : (0 : ℝ) ≤ p), Real.rpow_natCast]
  have hnat : (p^(r*H) : ℝ)^δ = ((p : ℝ)^H)^(ε/2) := by
    rw [Nat.mul_comm r H,pow_mul,← Real.rpow_natCast _ r,← Real.rpow_mul (by positivity),hδeq]
  have hpow : (((p : ℝ)^H)^(ε/4)*((p : ℝ)^H)^(ε/4))*((p : ℝ)^H)^(ε/2) =
      ((p : ℝ)^H)^ε := by
    rw [← Real.rpow_add (by positivity),← Real.rpow_add (by positivity)]
    congr 1
    ring
  calc
    (1+(H : ℝ)*(p : ℝ)^c)^n*(p^(r*H) : ℝ)^δ ≤
        ((1+(H : ℝ))*(p : ℝ)^c)^n*(p^(r*H) : ℝ)^δ := by gcongr
    _ = (1+(H : ℝ))^n*((p : ℝ)^c)^n*((p : ℝ)^H)^(ε/2) := by rw [mul_pow,hnat]
    _ ≤ (A*((p : ℝ)^H)^(ε/4))*((p : ℝ)^(2*n)*((p : ℝ)^H)^(ε/4))*
        ((p : ℝ)^H)^(ε/2) := by gcongr; exact hpoly H
    _ = D*((((p : ℝ)^H)^(ε/4)*((p : ℝ)^H)^(ε/4))*((p : ℝ)^H)^(ε/2)) := by dsimp [D]; ring
    _ = _ := by rw [hpow]

#print axioms sparse_partition_epsilon_parameters

end WaringSiegel.WSL3
