import Waring.EndgameCompletionTwistedPrime
import Waring.EndgameCompletionPowerFibers

/-!
# Twisted stationary phase and derivative fibers

The linear twist survives in the exact derivative condition.  Power-fiber
counting includes nonunit targets; no nonsingularity of the exponent is
assumed at the prime.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.EndgameCompletion

theorem twistedMonomialSumMod_stationary_filter (q M : ℕ) [NeZero q]
    (hM : 0 < M) (k : ℕ) (a b h : ZMod q) (hh : h^2=0)
    (hMh : (M : ZMod q)*h=0) :
    twistedMonomialSumMod q k a b =
      ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter
        (fun x => (a*(k : ZMod q)*x^(k-1)+b)*h=0),
        ZMod.stdAddChar (a*x^k+b*x) := by
  have hshift (t : ℕ) :
      (∑ x : ZMod q, ZMod.stdAddChar
        (a*(x+h*(t : ZMod q))^k+b*(x+h*(t : ZMod q)))) =
        twistedMonomialSumMod q k a b := by
    unfold twistedMonomialSumMod
    exact Fintype.sum_equiv (Equiv.addRight (h*(t : ZMod q))) _ _ (fun _ => rfl)
  have hlinear (x : ZMod q) :
      (∑ t ∈ Finset.range M, ZMod.stdAddChar
        (((a*(k : ZMod q)*x^(k-1)+b)*h)*(t : ZMod q))) =
        if (a*(k : ZMod q)*x^(k-1)+b)*h=0 then (M : ℂ) else 0 := by
    apply stdAddChar_sum_range
    calc
      _ = (a*(k : ZMod q)*x^(k-1)+b)*((M : ZMod q)*h) := by ring
      _ = 0 := by rw [hMh,mul_zero]
  have havg : (M : ℂ)*twistedMonomialSumMod q k a b =
      ∑ x : ZMod q, ZMod.stdAddChar (a*x^k+b*x)*
        (∑ t ∈ Finset.range M, ZMod.stdAddChar
          (((a*(k : ZMod q)*x^(k-1)+b)*h)*(t : ZMod q))) := by
    calc
      _ = ∑ _t ∈ Finset.range M, twistedMonomialSumMod q k a b := by simp
      _ = ∑ t ∈ Finset.range M, ∑ x : ZMod q, ZMod.stdAddChar
          (a*(x+h*(t : ZMod q))^k+b*(x+h*(t : ZMod q))) :=
        Finset.sum_congr rfl (fun t _ => (hshift t).symm)
      _ = ∑ x : ZMod q, ∑ t ∈ Finset.range M, ZMod.stdAddChar
          (a*(x+h*(t : ZMod q))^k+b*(x+h*(t : ZMod q))) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        have hht : (h*(t : ZMod q))^2=0 := by rw [mul_pow,hh,zero_mul]
        rw [add_pow_of_sq_zero x (h*(t : ZMod q)) hht]
        have heq : a*(x^k+(k : ZMod q)*x^(k-1)*(h*t))+b*(x+h*t) =
            (a*x^k+b*x)+((a*k*x^(k-1)+b)*h)*t := by ring
        rw [heq,AddChar.map_add_eq_mul]
  simp_rw [hlinear] at havg
  apply mul_left_cancel₀ (a := (M : ℂ)) (by exact_mod_cast Nat.ne_of_gt hM)
  calc
    _ = ∑ x : ZMod q, ZMod.stdAddChar (a*x^k+b*x)*
        (if (a*(k : ZMod q)*x^(k-1)+b)*h=0 then (M : ℂ) else 0) := havg
    _ = _ := by
      rw [Finset.mul_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp [mul_comm]

theorem twistedMonomialSumMod_primepower_filter {p : ℕ} [Fact p.Prime]
    (l j k : ℕ) (hj : 2*j ≤ l) (a b : ZMod (p^l)) :
    twistedMonomialSumMod (p^l) k a b =
      ∑ x ∈ (Finset.univ : Finset (ZMod (p^l))).filter
        (fun x => (a*(k : ZMod (p^l))*x^(k-1)+b)*(p^(l-j) : ℕ)=0),
        ZMod.stdAddChar (a*x^k+b*x) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply twistedMonomialSumMod_stationary_filter (p^l) (p^j) (pow_pos hp j)
  · rw [← Nat.cast_pow,ZMod.natCast_eq_zero_iff,← pow_mul]
    exact pow_dvd_pow p (by omega)
  · rw [← Nat.cast_mul,← pow_add,show j+(l-j)=l by omega,ZMod.natCast_self]

/-- The complete lift of a residue predicate has at most M times as many
points when q=M*d. The proof records residue and quotient explicitly. -/
theorem card_zmod_reduction_le (q d M : ℕ) [NeZero q] [NeZero d]
    (hd : 0<d) (hq : q=M*d) (P : ZMod d → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : ZMod q => P (x.val : ZMod d)).card ≤
      M*(Finset.univ.filter P).card := by
  have hle : (Finset.univ.filter fun x : ZMod q => P (x.val : ZMod d)).card ≤
      ((Finset.univ.filter P) ×ˢ Finset.range M).card := by
    apply Finset.card_le_card_of_injOn (fun x : ZMod q => ((x.val : ZMod d),x.val/d))
    · intro x hx
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩,?_⟩
      apply Finset.mem_range.mpr
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa only [← hq] using x.val_lt
    · intro x _ y _ hxy
      apply ZMod.val_injective
      have hmod : x.val%d=y.val%d :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).mp (congrArg Prod.fst hxy)
      have hdiv : x.val/d=y.val/d := congrArg Prod.snd hxy
      calc
        x.val=x.val%d+d*(x.val/d) := (Nat.mod_add_div _ _).symm
        _ = y.val%d+d*(y.val/d) := by rw [hmod,hdiv]
        _ = y.val := Nat.mod_add_div _ _
  simpa only [Finset.card_product,Finset.card_range,Nat.mul_comm] using hle

/-- A linear congruence with positive natural coefficient m has at most m
residues, even when m shares factors with the modulus. -/
theorem card_linear_zmod_le (q m : ℕ) [NeZero q] (hm : 0<m) (b : ZMod q) :
    (Finset.univ.filter fun x : ZMod q => (m : ZMod q)*x=b).card ≤ m := by
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  apply (Finset.card_le_card_of_injOn (s := Finset.univ.filter
    fun x : ZMod q => (m : ZMod q)*x=b) (t := Finset.range m)
    (fun x => (m*x.val)/q) ?_ ?_).trans_eq (Finset.card_range m)
  · intro x _
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hq).mpr (Nat.mul_lt_mul_of_pos_left x.val_lt hm)
  · intro x hx y hy hxy
    change (m*x.val)/q=(m*y.val)/q at hxy
    apply ZMod.val_injective
    have hcast : ((m*x.val : ℕ) : ZMod q)=((m*y.val : ℕ) : ZMod q) := by
      simpa only [Nat.cast_mul,ZMod.natCast_zmod_val] using
        (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
    apply Nat.eq_of_mul_eq_mul_left hm
    calc
      m*x.val=(m*x.val)%q+q*((m*x.val)/q) := (Nat.mod_add_div _ _).symm
      _ = (m*y.val)%q+q*((m*y.val)/q) := by rw [hmod,hxy]
      _ = m*y.val := Nat.mod_add_div _ _

theorem card_unit_linear_zmod_le (q m : ℕ) [NeZero q] (hm : 0<m)
    (a : (ZMod q)ˣ) (b : ZMod q) :
    (Finset.univ.filter fun x : ZMod q => (a : ZMod q)*m*x=b).card ≤ m := by
  apply (Finset.card_le_card_of_injOn (t := Finset.univ.filter
    fun x : ZMod q => (m : ZMod q)*x=b) (fun x : ZMod q => (a : ZMod q)*x) ?_ ?_).trans
    (card_linear_zmod_le q m hm b)
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa only [mul_assoc,mul_comm,mul_left_comm] using (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact a.isUnit.mul_left_cancel hxy

/-- Multiplication modulo q cannot remove a common divisor with q. -/
theorem gcd_val_dvd_gcd_mul (q : ℕ) [NeZero q] (a b : ZMod q) :
    Nat.gcd b.val q ∣ Nat.gcd (a*b).val q := by
  apply Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
  have heq : a*b=((a.val*b.val : ℕ) : ZMod q) := by
    rw [Nat.cast_mul,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  rw [heq,dvd_zmod_val_iff_dvd (Nat.gcd_dvd_right _ _)]
  exact (Nat.gcd_dvd_left _ _).mul_left _

/-- Derivative binomials at every prime, including singular exponent primes. -/
theorem primepower_scaled_power_fiber_card_le {p d m : ℕ} (hp : p.Prime)
    (hd : 0<d) (hm : 0<m) (l : ℕ) [NeZero (p^l)]
    (a : (ZMod (p^l))ˣ) (b : ZMod (p^l)) :
    (Finset.univ.filter fun x : ZMod (p^l) => (a : ZMod (p^l))*m*x^d=b).card ≤
      (2*d*m)*Nat.gcd b.val (p^l) := by
  let A := Finset.univ.filter fun x : ZMod (p^l) => (a : ZMod (p^l))*m*x^d=b
  let B := Finset.univ.filter fun z : ZMod (p^l) => (a : ZMod (p^l))*m*z=b
  have hmap : ∀x∈A,x^d∈B := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
  have hgcpos : 0<Nat.gcd b.val (p^l) := Nat.gcd_pos_of_pos_right _ (pow_pos hp.pos _)
  have hfiber (z : ZMod (p^l)) (hz : z∈B) :
      (A.filter fun x => x^d=z).card ≤ 2*d*Nat.gcd b.val (p^l) := by
    have hzgcd : Nat.gcd z.val (p^l)≤Nat.gcd b.val (p^l) := by
      apply Nat.le_of_dvd hgcpos
      have hh := gcd_val_dvd_gcd_mul (p^l) ((a : ZMod (p^l))*m) z
      rwa [(Finset.mem_filter.mp hz).2] at hh
    calc
      _ ≤ (Finset.univ.filter fun x : ZMod (p^l) => x^d=z).card :=
        Finset.card_le_card (by
          intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩)
      _ ≤ 2*d*Nat.gcd z.val (p^l) := primepower_power_fiber_card_le hp hd l z
      _ ≤ _ := Nat.mul_le_mul_left _ hzgcd
  change A.card≤_
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _z ∈ B, 2*d*Nat.gcd b.val (p^l) := Finset.sum_le_sum hfiber
    _ = B.card*(2*d*Nat.gcd b.val (p^l)) := by simp
    _ ≤ m*(2*d*Nat.gcd b.val (p^l)) := Nat.mul_le_mul_right _
      (card_unit_linear_zmod_le (p^l) m hm a b)
    _ = _ := by ring

theorem gcd_zmod_neg_val (q : ℕ) [NeZero q] (b : ZMod q) :
    Nat.gcd (-b).val q=Nat.gcd b.val q := by
  apply Nat.dvd_antisymm
  · simpa only [neg_one_mul,neg_neg] using gcd_val_dvd_gcd_mul q (-1) (-b)
  · simpa only [neg_one_mul] using gcd_val_dvd_gcd_mul q (-1) b

theorem gcd_zmod_reduce_le {q d : ℕ} [NeZero q] [NeZero d]
    (hdq : d∣q) (b : ZMod q) :
    Nat.gcd ((b.val : ZMod d).val) d ≤ Nat.gcd b.val q := by
  rw [ZMod.val_natCast]
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne q)))
  apply Nat.dvd_gcd
  · have hh := Nat.gcd_dvd_left (b.val%d) d
    exact (Nat.dvd_mod_iff (Nat.gcd_dvd_right _ _)).mp hh
  · exact (Nat.gcd_dvd_right _ _).trans hdq

/-- A uniform bound after square-zero averaging; all singular derivative
fibers are covered by the gcd of the linear twist. -/
theorem norm_twistedMonomialSumMod_primepower_le {p : ℕ} [Fact p.Prime]
    (l j k : ℕ) (hk : 2≤k) (hj : 2*j≤l)
    (a : (ZMod (p^l))ˣ) (b : ZMod (p^l)) :
    ‖twistedMonomialSumMod (p^l) k (a : ZMod (p^l)) b‖ ≤
      (p^(l-j) : ℕ)*(2*(k-1)*k : ℕ)*Nat.gcd b.val (p^l) := by
  have hp := (Fact.out : p.Prime)
  have hjl : j≤l := by omega
  let π : ZMod (p^l) →+* ZMod (p^j) := ZMod.castHom (pow_dvd_pow p hjl) (ZMod (p^j))
  have hπ (z : ZMod (p^l)) : π z=(z.val : ZMod (p^j)) := by
    calc
      _ = π ((z.val : ℕ) : ZMod (p^l)) := by rw [ZMod.natCast_zmod_val]
      _ = _ := map_natCast _ _
  let a' : (ZMod (p^j))ˣ := Units.map π.toMonoidHom a
  let b' := π b
  have ha' : (a' : ZMod (p^j))=π (a : ZMod (p^l)) := rfl
  let B := Finset.univ.filter fun y : ZMod (p^j) =>
    (a' : ZMod (p^j))*k*y^(k-1)= -b'
  have hiff (x : ZMod (p^l)) :
      (((a : ZMod (p^l))*k*x^(k-1)+b)*(p^(l-j) : ℕ)=0) ↔
      (a' : ZMod (p^j))*k*(x.val : ZMod (p^j))^(k-1)= -b' := by
    rw [primepower_annihilator_power_iff l j hjl]
    rw [← ZMod.natCast_eq_zero_iff,← hπ]
    simp only [map_add,map_mul,map_pow,map_natCast,← ha',hπ x]
    exact add_eq_zero_iff_eq_neg
  have hcard : (Finset.univ.filter fun x : ZMod (p^l) =>
      ((a : ZMod (p^l))*k*x^(k-1)+b)*(p^(l-j) : ℕ)=0).card ≤
      p^(l-j)*(2*(k-1)*k)*Nat.gcd b.val (p^l) := by
    simp_rw [hiff]
    calc
      _ ≤ p^(l-j)*B.card := by
        exact card_zmod_reduction_le (p^l) (p^j) (p^(l-j))
          (pow_pos hp.pos _) (by rw [← pow_add,Nat.sub_add_cancel hjl])
          (fun y : ZMod (p^j) => (a' : ZMod (p^j))*k*y^(k-1)= -b')
      _ ≤ p^(l-j)*((2*(k-1)*k)*Nat.gcd (-b').val (p^j)) :=
        Nat.mul_le_mul_left _ (primepower_scaled_power_fiber_card_le hp
          (by omega : 0<k-1) (by omega : 0<k) j a' (-b'))
      _ ≤ p^(l-j)*((2*(k-1)*k)*Nat.gcd b.val (p^l)) := by
        rw [gcd_zmod_neg_val]
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        simpa only [b',hπ] using gcd_zmod_reduce_le (pow_dvd_pow p hjl) b
      _ = _ := by ring
  rw [twistedMonomialSumMod_primepower_filter l j k hj]
  calc
    _ ≤ ∑ x ∈ (Finset.univ : Finset (ZMod (p^l))).filter
        (fun x => ((a : ZMod (p^l))*k*x^(k-1)+b)*(p^(l-j) : ℕ)=0),
        ‖ZMod.stdAddChar ((a : ZMod (p^l))*x^k+b*x)‖ := norm_sum_le _ _
    _ = ((Finset.univ.filter fun x : ZMod (p^l) =>
        ((a : ZMod (p^l))*k*x^(k-1)+b)*(p^(l-j) : ℕ)=0).card : ℝ) := by
      simp
    _ ≤ _ := by exact_mod_cast hcard

/-- The elementary exponent 3/4 holds at every prime-power level l>=2.
It uses only a square-zero average and finite root counting. -/
theorem twistedMonomialSumMod_primepower_fourth_le {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hl : 2≤l) (hk : 2≤k)
    (a : (ZMod (p^l))ˣ) (b : ZMod (p^l)) :
    ‖twistedMonomialSumMod (p^l) k (a : ZMod (p^l)) b‖^4 ≤
      (2*(k-1)*k : ℕ)^4*(p^l : ℕ)^3*(Nat.gcd b.val (p^l) : ℕ)^4 := by
  have hp := (Fact.out : p.Prime)
  have hbound := norm_twistedMonomialSumMod_primepower_le l (l/2) k hk
    (Nat.mul_div_le l 2) a b
  have hexp : 4*(l-l/2)≤3*l := by omega
  have hpower : (p^(l-l/2) : ℕ)^4 ≤ (p^l : ℕ)^3 := by
    rw [← pow_mul,← pow_mul]
    exact Nat.pow_le_pow_right hp.one_le (by omega)
  calc
    _ ≤ ((p^(l-l/2) : ℕ)*(2*(k-1)*k : ℕ)*Nat.gcd b.val (p^l) : ℝ)^4 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 4
    _ = (2*(k-1)*k : ℕ)^4*(p^(l-l/2) : ℕ)^4*(Nat.gcd b.val (p^l) : ℕ)^4 := by ring
    _ ≤ _ := by
      gcongr
      exact_mod_cast hpower

/-- Uniform positive prime-power levels, combining the prime fourth moment
with the exact stationary-phase estimate for higher powers. -/
theorem twistedMonomialSumMod_primepower_fourth_uniform {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hl : 1≤l) (hk : 2≤k)
    (a : (ZMod (p^l))ˣ) (b : ZMod (p^l)) :
    ‖twistedMonomialSumMod (p^l) k (a : ZMod (p^l)) b‖^4 ≤
      (2*k^2 : ℕ)^4*(p^l : ℕ)^3*(Nat.gcd b.val (p^l) : ℕ)^4 := by
  have hp := (Fact.out : p.Prime)
  have hc : (1 : ℝ)≤(2*k^2 : ℕ) := by exact_mod_cast (by nlinarith : 1≤2*k^2)
  by_cases hl2 : 2≤l
  · apply (twistedMonomialSumMod_primepower_fourth_le l k hl2 hk a b).trans
    have hC : ((2*(k-1)*k : ℕ) : ℝ)≤(2*k^2 : ℕ) := by
      exact_mod_cast (show 2*(k-1)*k≤2*k^2 by nlinarith [Nat.sub_le k 1])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hC 4) (by positivity)) (by positivity)
  · have hl1 : l=1 := by omega
    subst l
    by_cases hb : b=0
    · have htriv := norm_twistedMonomialSumMod_le (p^1) k (a : ZMod (p^1)) b
      have hgc : Nat.gcd b.val (p^1)=p := by simp [hb]
      rw [hgc]
      simp only [pow_one] at htriv ⊢
      calc
        _ ≤ (p : ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _) htriv 4
        _ ≤ (2*k^2 : ℕ)^4*(p : ℝ)^3*(p : ℝ)^4 := by
          have hp1 : (1 : ℝ)≤p := by exact_mod_cast hp.one_le
          have hC4 : (1 : ℝ)≤(2*k^2 : ℕ)^4 := one_le_pow₀ hc
          have hp3 : (1 : ℝ)≤(p : ℝ)^3 := one_le_pow₀ hp1
          exact le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hC4 hp3)
    · letI : Fact (Nat.Prime (p^1)) := ⟨by simpa only [pow_one] using hp⟩
      have hprime := twistedMonomialSumMod_prime_fourth_le k hk
        (a : ZMod (p^1)) b hb
      simp only [pow_one] at hprime
      have hgc1 : (1 : ℝ)≤(Nat.gcd b.val (p^1) : ℕ) := by
        exact_mod_cast Nat.gcd_pos_of_pos_right b.val (pow_pos hp.pos 1)
      simp only [pow_one] at hgc1
      have hkR : (2 : ℝ)≤k := by exact_mod_cast hk
      have hC : 2*(k+1 : ℝ)≤(2*k^2 : ℕ)^4 := by
        have hbase : 2*(k+1 : ℝ)≤(2*k^2 : ℕ) := by push_cast; nlinarith
        have hpw : (2*k^2 : ℕ)≤((2*k^2 : ℕ) : ℝ)^4 :=
          le_self_pow₀ hc (by norm_num : 4≠0)
        exact hbase.trans hpw
      calc
        _ ≤ 2*(k+1 : ℝ)*(p : ℝ)^3 := hprime
        _ ≤ (2*k^2 : ℕ)^4*(p : ℝ)^3 := mul_le_mul_of_nonneg_right hC (by positivity)
        _ ≤ _ := by
          simp only [pow_one]
          exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hgc1)

#print axioms twistedMonomialSumMod_primepower_filter
#print axioms primepower_scaled_power_fiber_card_le
#print axioms twistedMonomialSumMod_primepower_fourth_le
#print axioms twistedMonomialSumMod_primepower_fourth_uniform

end Waring.EndgameCompletion
