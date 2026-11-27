import Waring.PolicyCompletionSmoothDecomposition
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Unique prime partitions and ordered smooth-factor windows

These exact factorizations underlie the smooth Weyl-sum decomposition on
restricted arcs. Uniqueness matters here: positivity of Fourier collision
counts on the full circle does not justify pointwise subsum enlargement on
an arc.
-/

noncomputable section
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments

def PrimeRestricted (S : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → S p

theorem primeRestricted_mul {S : ℕ → Prop} {u v : ℕ}
    (hu : PrimeRestricted S u) (hv : PrimeRestricted S v) :
    PrimeRestricted S (u*v) := by
  intro p hp hpd
  exact (hp.dvd_mul.mp hpd).elim (hu p hp) (hv p hp)

theorem primeRestricted_one (S : ℕ → Prop) : PrimeRestricted S 1 := by
  intro p hp hpd
  exact False.elim (by have := Nat.le_of_dvd (by norm_num : 0 < 1) hpd; have := hp.two_le; omega)

theorem exists_prime_partition (S : ℕ → Prop) (n : ℕ) (hn : 0 < n) :
    ∃ u v : ℕ, n=u*v ∧ PrimeRestricted S u ∧ PrimeRestricted (fun p => ¬S p) v := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n=1
    · exact ⟨1,1,by simpa using hn1,primeRestricted_one S,primeRestricted_one _⟩
    obtain ⟨p,hp,hpn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨m,hnm⟩ := hpn
    have hmpos : 0 < m := by
      by_contra h
      have hm0 : m=0 := by omega
      simp only [hm0,mul_zero] at hnm
      omega
    have hmlt : m < n := by
      rw [hnm]
      exact lt_mul_of_one_lt_left hmpos hp.one_lt
    obtain ⟨u,v,hmuv,hu,hv⟩ := ih m hmlt hmpos
    by_cases hSp : S p
    · refine ⟨p*u,v,?_,primeRestricted_mul ?_ hu,hv⟩
      · rw [hnm,hmuv,mul_assoc]
      · intro q hq hqp
        exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp ▸ hSp
    · refine ⟨u,p*v,?_,hu,primeRestricted_mul ?_ hv⟩
      · rw [hnm,hmuv]; ring
      · intro q hq hqp
        exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp ▸ hSp

theorem disjoint_prime_coprime {S : ℕ → Prop} {u v : ℕ}
    (hu : PrimeRestricted S u) (hv : PrimeRestricted (fun p => ¬S p) v) : u.Coprime v :=
  Nat.coprime_of_dvd (fun p hp hpu hpv => hv p hp hpv (hu p hp hpu))

/-- The prime partition is literally unique, including all prime powers. -/
theorem prime_partition_unique {S : ℕ → Prop} {u v u' v' : ℕ}
    (hu : 0 < u) (heq : u*v=u'*v')
    (hSu : PrimeRestricted S u) (hSv : PrimeRestricted (fun p => ¬S p) v)
    (hSu' : PrimeRestricted S u') (hSv' : PrimeRestricted (fun p => ¬S p) v') :
    u=u' ∧ v=v' := by
  have huvd : u ∣ u'*v' := by rw [← heq]; exact dvd_mul_right u v
  have hu'vd : u' ∣ u*v := by rw [heq]; exact dvd_mul_right u' v'
  have huu' := (disjoint_prime_coprime hSu hSv').dvd_of_dvd_mul_right huvd
  have hu'u := (disjoint_prime_coprime hSu' hSv).dvd_of_dvd_mul_right hu'vd
  have huueq : u=u' := Nat.dvd_antisymm huu' hu'u
  refine ⟨huueq,?_⟩
  rw [← huueq] at heq
  exact Nat.eq_of_mul_eq_mul_left hu heq

theorem coprime_supported_factorization_unique {q w u w' u' : ℕ}
    (hw : 0 < w) (heq : w*u=w'*u') (hwq : w.Coprime q) (hwq' : w'.Coprime q)
    (hu : PrimeRestricted (fun p => p ∣ q) u)
    (hu' : PrimeRestricted (fun p => p ∣ q) u') : w=w' ∧ u=u' := by
  apply prime_partition_unique (S := fun p => ¬p ∣ q) hw heq
  · intro p hp hpw hpq
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpw hpq hwq
  · intro p hp hpu hnot
    exact hnot (hu p hp hpu)
  · intro p hp hpw hpq
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpw hpq hwq'
  · intro p hp hpu hnot
    exact hnot (hu' p hp hpu)

/-- Every integer larger than M has a window factor obtained by removing
its least prime repeatedly. The remaining quotient has no prime above the
last removed threshold, and the window factor has none below it. -/
theorem exists_ordered_window (n : ℕ) {M : ℝ} (hM : 1 ≤ M) (hnM : M < (n : ℝ)) :
    ∃ π m w : ℕ, π.Prime ∧ n=m*w ∧ π ∣ m ∧
      M < (m : ℝ) ∧ (m : ℝ) ≤ M*(π : ℝ) ∧
      PrimeRestricted (fun p => π ≤ p) m ∧ IsSmooth w (π : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn1 : n ≠ 1 := by intro h; subst n; norm_num at hnM; linarith
    have hnpos : 0 < n := by exact_mod_cast (zero_lt_one.trans_le hM |>.trans hnM)
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    obtain ⟨a,hna⟩ := Nat.minFac_dvd n
    have ha : 0 < a := by
      by_contra h
      have ha0 : a=0 := by omega
      simp only [ha0,mul_zero] at hna
      omega
    have halt : a < n := by
      rw [hna]
      exact lt_mul_of_one_lt_left ha hp.one_lt
    by_cases hMa : M < (a : ℝ)
    · obtain ⟨π,m,w,hπ,hamw,hπm,hMm,hmM,hrough,hsmooth⟩ := ih a halt hMa
      have hπn : π ∣ n := by
        apply hπm.trans
        refine ⟨p*w,?_⟩
        rw [hna,hamw]
        ring
      have hpπ : p ≤ π := Nat.minFac_le_of_dvd hπ.two_le hπn
      refine ⟨π,m,w*p,hπ,?_,hπm,hMm,hmM,hrough,?_⟩
      · rw [hna,hamw]; ring
      · intro q hq hqd
        rcases hq.dvd_mul.mp hqd with hqw | hqp
        · exact hsmooth q hq hqw
        · have hqp' : q=p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
          exact_mod_cast hqp' ▸ hpπ
    · refine ⟨p,n,1,hp,by simp,Nat.minFac_dvd n,hnM,?_,?_,?_⟩
      · have haM : (a : ℝ) ≤ M := le_of_not_gt hMa
        have hcast : (n : ℝ)=(p : ℝ)*(a : ℝ) := by exact_mod_cast hna
        rw [hcast]
        nlinarith [show (0 : ℝ) ≤ p by positivity]
      · intro q hq hqd
        exact Nat.minFac_le_of_dvd hq.two_le hqd
      · intro q hq hqd
        exact False.elim (by have := Nat.le_of_dvd (by norm_num : 0 < 1) hqd; have := hq.two_le; omega)

#print axioms prime_partition_unique
#print axioms exists_ordered_window
end Waring.RestrictedSmoothFactorization
