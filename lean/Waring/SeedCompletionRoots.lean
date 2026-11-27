import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# Nonsingular polynomial congruences

The first efficient-differencing argument bounds the number of nonsingular
roots of an integral polynomial modulo a prime power. The central uniqueness
step is elementary: the quadratic Taylor remainder shows that two such roots
in the same residue class modulo the prime agree modulo its full power.

This is one arithmetic prerequisite of the analytic source theorem. It is not
an assertion of an efficient-differencing inequality or a smooth-moment seed.
-/

noncomputable section

namespace Waring.SeedCompletion

/-- If a polynomial has derivative coprime to a modulus at `x`, then its
congruence class modulo every power of that modulus distinguishes points in
the residue class of `x`. No primality assumption is needed for this step. -/
theorem nonsingular_congruence_power_unique {R : Type*} [CommRing R]
    (f : Polynomial R) (p x y : R) (e : ℕ)
    (hcop : IsCoprime p (f.derivative.eval x))
    (hxy : p ∣ y - x) (hf : p ^ e ∣ f.eval y - f.eval x) :
    p ^ e ∣ y - x := by
  obtain ⟨q, hq⟩ := f.binomExpansion x (y - x)
  have heq : f.eval y - f.eval x =
      (f.derivative.eval x + q * (y - x)) * (y - x) := by
    have hadd : x + (y - x) = y := by ring
    have hq' : f.eval y = f.eval x + f.derivative.eval x * (y - x) +
        q * (y - x) ^ 2 := by simpa only [hadd] using hq
    rw [hq']
    ring
  have hcop' : IsCoprime p (f.derivative.eval x + q * (y - x)) := by
    obtain ⟨t, ht⟩ := hxy
    rw [ht]
    convert hcop.add_mul_left_right (q * t) using 1
    ring
  exact hcop'.pow_left.dvd_of_dvd_mul_left (heq ▸ hf)

/-- Canonical natural representatives of nonsingular roots modulo `p^e`. -/
def nonsingularResidueRoots (f : Polynomial ℤ) (a : ℤ) (p e : ℕ) : Finset ℕ :=
  (Finset.range (p ^ e)).filter fun x =>
    (p : ℤ) ^ e ∣ f.eval (x : ℤ) - a ∧
      IsCoprime (p : ℤ) (f.derivative.eval (x : ℤ))

theorem mem_nonsingularResidueRoots {f : Polynomial ℤ} {a : ℤ} {p e x : ℕ} :
    x ∈ nonsingularResidueRoots f a p e ↔
      x < p ^ e ∧ (p : ℤ) ^ e ∣ f.eval (x : ℤ) - a ∧
        IsCoprime (p : ℤ) (f.derivative.eval (x : ℤ)) := by
  classical
  simp [nonsingularResidueRoots]

/-- Reduction modulo the underlying modulus is injective on these roots. -/
theorem nonsingularResidueRoots_reduction_injective
    (f : Polynomial ℤ) (a : ℤ) (p e : ℕ) :
    Set.InjOn (fun x : ℕ => (x : ZMod p)) (nonsingularResidueRoots f a p e) := by
  intro x hx y hy hxy
  obtain ⟨hxlt, hfx, hcopx⟩ := mem_nonsingularResidueRoots.mp hx
  obtain ⟨hylt, hfy, _⟩ := mem_nonsingularResidueRoots.mp hy
  have hdiv : (p : ℤ) ∣ (y : ℤ) - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) p).mp (by simpa using hxy)
  have hfdiv : (p : ℤ) ^ e ∣ f.eval (y : ℤ) - f.eval (x : ℤ) := by
    convert dvd_sub hfy hfx using 1
    ring
  have hpow := nonsingular_congruence_power_unique f (p : ℤ) (x : ℤ) (y : ℤ) e
    hcopx hdiv hfdiv
  have hcast : (x : ZMod (p ^ e)) = (y : ZMod (p ^ e)) := by
    have hdiv' : ((p ^ e : ℕ) : ℤ) ∣ (y : ℤ) - x := by
      simpa only [Nat.cast_pow] using hpow
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) (p ^ e)).mpr hdiv'
  have hmod := (ZMod.natCast_eq_natCast_iff' x y (p ^ e)).mp hcast
  simpa only [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hmod

/-- Every prime power has at most the degree many nonsingular solutions of
one polynomial congruence. The bound is uniform in the power and target. -/
theorem nonsingularResidueRoots_card_le_natDegree
    (f : Polynomial ℤ) (a : ℤ) {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    (nonsingularResidueRoots f a p e).card ≤ f.natDegree := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let c : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let g : Polynomial (ZMod p) := f.map c - Polynomial.C (a : ZMod p)
  have heval (x : ℕ) : (f.map c).eval (x : ZMod p) = c (f.eval (x : ℤ)) :=
    Polynomial.eval_natCast_map c f x
  have hderiv (x : ℕ) : g.derivative.eval (x : ZMod p) =
      c (f.derivative.eval (x : ℤ)) := by
    simp only [g, Polynomial.derivative_sub, Polynomial.derivative_C,
      sub_zero, Polynomial.derivative_map]
    exact Polynomial.eval_natCast_map c f.derivative x
  by_cases hs : (nonsingularResidueRoots f a p e).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hs
    have hcop := (mem_nonsingularResidueRoots.mp hx₀).2.2
    have hunit : IsUnit (g.derivative.eval (x₀ : ZMod p)) := by
      rw [hderiv]
      have hc := hcop.map c
      simpa [c] using hc
    have hg : g ≠ 0 := by
      intro hz
      have hn := hunit.ne_zero
      exact hn (by simp [hz])
    have hroots : ((nonsingularResidueRoots f a p e).image (fun x : ℕ => (x : ZMod p))).val
        ⊆ g.roots := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hfx := (mem_nonsingularResidueRoots.mp hx).2.1
      have hpdiv : (p : ℤ) ∣ f.eval (x : ℤ) - a :=
        (dvd_pow_self (p : ℤ) (Nat.ne_of_gt he)).trans hfx
      apply (Polynomial.mem_roots hg).mpr
      change g.eval (x : ZMod p) = 0
      rw [show g = f.map c - Polynomial.C (a : ZMod p) from rfl,
        Polynomial.eval_sub, Polynomial.eval_C, heval]
      change (↑(f.eval (x : ℤ)) : ZMod p) - (a : ZMod p) = 0
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (x : ℤ) - a) p).mpr hpdiv
    calc
      (nonsingularResidueRoots f a p e).card =
          ((nonsingularResidueRoots f a p e).image (fun x : ℕ => (x : ZMod p))).card :=
        (Finset.card_image_of_injOn (nonsingularResidueRoots_reduction_injective f a p e)).symm
      _ ≤ g.natDegree := Polynomial.card_le_degree_of_subset_roots hroots
      _ ≤ f.natDegree := by
        calc
          g.natDegree ≤ max (f.map c).natDegree (Polynomial.C (a : ZMod p)).natDegree :=
            Polynomial.natDegree_sub_le _ _
          _ = (f.map c).natDegree := by simp
          _ ≤ f.natDegree := Polynomial.natDegree_map_le
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.zero_le]

#print axioms nonsingular_congruence_power_unique
#print axioms nonsingularResidueRoots_reduction_injective
#print axioms nonsingularResidueRoots_card_le_natDegree

end Waring.SeedCompletion
