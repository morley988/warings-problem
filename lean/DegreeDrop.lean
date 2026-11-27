import Std

/-! The integer arithmetic in Lemma 3.1 of Chow–Dietmann, arXiv:2611.29821v1.
The parameter `D` and the exponents `e` are arbitrary natural numbers.
A factor is a pair (base, exponent). Distinctness and primality are unnecessary
for these multiplicative inequalities and the divisibility assertion. -/
namespace WaringLinear

def step (D e : Nat) : Nat := max 1 ((2*e + 2*D) / (2*D+1))

def residual (D e : Nat) : Nat := e - D * step D e

theorem ceiling_bounds (D e : Nat) :
    2*e ≤ (2*D+1) * step D e ∧ (2*D+1) * step D e ≤ 2*e + (2*D+1) := by
  let n := 2*e + 2*D
  let d := 2*D+1
  have hd : 0 < d := by dsimp [d]; omega
  have lo := Nat.lt_mul_div_succ n hd
  have hi := Nat.mul_div_le n d
  rw [Nat.mul_add, Nat.mul_one] at lo
  change 2*e ≤ d * max 1 (n/d) ∧ d * max 1 (n/d) ≤ 2*e + d
  by_cases h : 1 ≤ n/d
  · rw [Nat.max_eq_right h]
    dsimp [d, n] at *
    omega
  · rw [Nat.max_eq_left (by omega), Nat.mul_one]
    have hn : n/d = 0 := Nat.eq_zero_of_not_pos h
    rw [hn, Nat.mul_zero] at lo
    dsimp [n, d] at *
    omega

theorem exponent_bounds (D e : Nat) :
    e ≤ (D+1) * step D e ∧
    (2*D+1) * residual D e ≤ e ∧
    e ≤ (2*D+1) * (residual D e + D) := by
  let s := step D e
  let t := residual D e
  obtain ⟨hl, hu⟩ := ceiling_bounds D e
  change 2*e ≤ (2*D+1)*s at hl
  change (2*D+1)*s ≤ 2*e + (2*D+1) at hu
  have hone : e ≤ (D+1)*s := by
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at hl ⊢
    omega
  have hd : D*s+t ≥ e := by change D*s+(e-D*s) ≥ e; omega
  have hlow' := Nat.mul_le_mul_left D hl
  have hs' : (2*D+1)*(D*s) = D*((2*D+1)*s) := by
    simp [Nat.mul_left_comm, Nat.mul_comm]
  have hu' := Nat.mul_le_mul_left D hu
  have hcross := Nat.mul_le_mul_left (2*D+1) hd
  rw [Nat.mul_add, hs', Nat.add_mul (2*D) 1 e, Nat.one_mul] at hcross
  have hDe : D*(2*e) = 2*D*e := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  rw [Nat.mul_add, hDe] at hu'
  refine ⟨hone, ?_, ?_⟩
  · by_cases h : D*s ≤ e
    · have heq : D*s+t = e := by change D*s+(e-D*s) = e; omega
      have htwo := congrArg (fun v => (2*D+1)*v) heq
      change (2*D+1)*(D*s+t) = (2*D+1)*e at htwo
      rw [Nat.mul_add, hs', Nat.add_mul (2*D) 1 e, Nat.one_mul] at htwo
      rw [hDe] at hlow'
      change (2*D+1)*t ≤ e
      omega
    · have hz : residual D e = 0 := by change e-D*s = 0; omega
      rw [hz, Nat.mul_zero]
      omega
  · change e ≤ (2*D+1)*(t+D)
    rw [Nat.mul_add, Nat.mul_comm (2*D+1) D]
    omega

def factorProduct (exponent : Nat → Nat) : List (Nat × Nat) → Nat
  | [] => 1
  | (p,e)::ps => p ^ exponent e * factorProduct exponent ps

theorem product_le_product (f g : Nat → Nat) (h : ∀ e, f e ≤ g e)
    (ps : List (Nat × Nat)) (hp : ∀ pe ∈ ps, 0 < pe.1) :
    factorProduct f ps ≤ factorProduct g ps := by
  induction ps with
  | nil => exact Nat.le_refl 1
  | cons pe ps ih =>
    rcases pe with ⟨p,e⟩
    apply Nat.mul_le_mul
    · exact Nat.pow_le_pow_right (hp (p,e) (by simp)) (h e)
    · exact ih (by intro pe hpe; exact hp pe (by simp [hpe]))

theorem product_dvd_product (f g : Nat → Nat) (h : ∀ e, f e ≤ g e)
    (ps : List (Nat × Nat)) : factorProduct f ps ∣ factorProduct g ps := by
  induction ps with
  | nil => exact Nat.dvd_refl 1
  | cons pe ps ih =>
    rcases pe with ⟨p,e⟩
    exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (h e)) ih

theorem product_scale (f : Nat → Nat) (n : Nat) (ps : List (Nat × Nat)) :
    factorProduct (fun e => n*f e) ps = (factorProduct f ps)^n := by
  induction ps with
  | nil => simp [factorProduct]
  | cons pe ps ih =>
    rcases pe with ⟨p,e⟩
    simp [factorProduct, Nat.mul_pow, ← ih, Nat.pow_mul, Nat.mul_comm n (f e)]

theorem product_add (f g : Nat → Nat) (ps : List (Nat × Nat)) :
    factorProduct (fun e => f e + g e) ps = factorProduct f ps * factorProduct g ps := by
  induction ps with
  | nil => simp [factorProduct]
  | cons pe ps ih =>
    rcases pe with ⟨p,e⟩
    simp [factorProduct, Nat.pow_add, ih, Nat.mul_left_comm, Nat.mul_assoc]

/-- Every higher coefficient in the expansion along a residue class has
denominator dividing its A^j factor. Multiplying by the integer binomial and
residue-class factors preserves this divisibility. -/
theorem degree_drop (D j : Nat) (hj : D < j) (ps : List (Nat × Nat)) :
    factorProduct id ps ∣ (factorProduct (step D) ps)^j := by
  rw [← product_scale]
  apply product_dvd_product
  intro e
  exact Nat.le_trans (exponent_bounds D e).1 (Nat.mul_le_mul_right _ hj)

/-- Multiplicative integer form of (3.3)–(3.4). Taking logarithms, dividing
by log X, and using positive bases recovers the inequalities of the paper. -/
theorem denominator_sandwich (D : Nat) (ps : List (Nat × Nat))
    (hp : ∀ pe ∈ ps, 0 < pe.1) :
    let q := factorProduct id ps
    let m := factorProduct (fun _ => 1) ps
    let A := factorProduct (step D) ps
    let qD := factorProduct (residual D) ps
    A^(2*D+1) ≤ q^2 * m^(2*D+1) ∧
    qD^(2*D+1) ≤ q ∧ q ≤ (qD*m^D)^(2*D+1) := by
  dsimp only
  constructor
  · rw [← product_scale, ← product_scale, ← product_scale, ← product_add]
    apply product_le_product _ _ _ ps hp
    intro e
    simpa using (ceiling_bounds D e).2
  constructor
  · rw [← product_scale]
    exact product_le_product _ _ (fun e => (exponent_bounds D e).2.1) ps hp
  · rw [← product_scale (fun _ => 1) D, ← product_add, ← product_scale]
    apply product_le_product _ _ _ ps hp
    intro e
    simpa using (exponent_bounds D e).2.2

theorem product_positive (f : Nat → Nat) (ps : List (Nat × Nat))
    (hp : ∀ pe ∈ ps, 0 < pe.1) : 0 < factorProduct f ps := by
  induction ps with
  | nil => exact Nat.zero_lt_one
  | cons pe ps ih =>
    rcases pe with ⟨p,e⟩
    apply Nat.mul_pos
    · exact Nat.pow_pos (hp (p,e) (by simp))
    · exact ih (by intro pe hpe; exact hp pe (by simp [hpe]))

theorem coprime_product (p : Nat) (f : Nat → Nat) (ps : List (Nat × Nat))
    (h : ∀ pe ∈ ps, p.Coprime pe.1) : p.Coprime (factorProduct f ps) := by
  induction ps with
  | nil => exact Nat.coprime_one_right _
  | cons pe ps ih =>
    rcases pe with ⟨q,e⟩
    apply Nat.Coprime.mul_right
    · exact (h (q,e) (by simp)).pow_right _
    · exact ih (by intro pe hpe; exact h pe (by simp [hpe]))

theorem gcd_pow_same (p a b : Nat) : Nat.gcd (p^a) (p^b) = p^(min a b) := by
  by_cases ha : a ≤ b
  · rw [Nat.min_eq_left ha]
    exact Nat.gcd_eq_left (Nat.pow_dvd_pow p ha)
  · have hb : b ≤ a := by omega
    rw [Nat.min_eq_right hb]
    exact Nat.gcd_eq_right (Nat.pow_dvd_pow p hb)

theorem product_gcd (f g : Nat → Nat) (ps : List (Nat × Nat))
    (hs : ps.Pairwise (fun u v => u.1.Coprime v.1)) :
    Nat.gcd (factorProduct f ps) (factorProduct g ps) =
      factorProduct (fun e => min (f e) (g e)) ps := by
  induction ps with
  | nil => simp [factorProduct]
  | cons pe ps ih =>
    rcases pe with ⟨p,e⟩
    obtain ⟨hd, ht⟩ := List.pairwise_cons.mp hs
    have hf := coprime_product p f ps hd
    have hg := coprime_product p g ps hd
    simp only [factorProduct]
    rw [(hf.pow_left _).mul_gcd, (hg.pow_left _).gcd_mul,
        (hg.pow_left _).gcd_mul, (hg.pow_left _).gcd_eq_one,
        (hf.pow_left _).symm.gcd_eq_one, Nat.mul_one, Nat.one_mul,
        gcd_pow_same, ih ht]

/-- Coprime products give the exact denominator after an arbitrary choice of
residue-class exponent f. -/
theorem reduced_denominator_for (D u : Nat) (f : Nat → Nat) (ps : List (Nat × Nat))
    (hs : ps.Pairwise (fun a b => a.1.Coprime b.1))
    (hp : ∀ pe ∈ ps, 0 < pe.1) (hu : u.Coprime (factorProduct id ps)) :
    let q := factorProduct id ps
    let A := factorProduct f ps
    q / Nat.gcd q (u*A^D) = factorProduct (fun e => e-D*f e) ps := by
  dsimp only
  rw [Nat.gcd_mul_right_right_of_gcd_eq_one hu.symm.gcd_eq_one,
      ← product_scale, product_gcd _ _ ps hs]
  let common := fun e => min e (D*f e)
  have split : (fun e => (e-D*f e) + common e) = id := by
    funext e
    simp only [id_eq, common]
    omega
  have hq := product_add (fun e => e-D*f e) common ps
  rw [split] at hq
  change factorProduct id ps / factorProduct common ps = _
  rw [hq, Nat.mul_div_cancel _ (product_positive _ ps hp)]

/-- The paper takes u = |a| * choose k D * n₀^(k-D). -/
theorem reduced_denominator (D u : Nat) (ps : List (Nat × Nat))
    (hs : ps.Pairwise (fun a b => a.1.Coprime b.1))
    (hp : ∀ pe ∈ ps, 0 < pe.1) (hu : u.Coprime (factorProduct id ps)) :
    let q := factorProduct id ps
    let A := factorProduct (step D) ps
    q / Nat.gcd q (u*A^D) = factorProduct (residual D) ps :=
  reduced_denominator_for D u (step D) ps hs hp hu

/-! Alternative arithmetic with rounding divisor D+1. -/

def stepOne (D e : Nat) : Nat := max 1 ((e+D)/(D+1))

theorem stepOne_bounds (D e : Nat) :
    let s := stepOne D e
    let t := e - D*s
    e ≤ (D+1)*s ∧ (D+1)*s ≤ e+(D+1) ∧
    (D+1)*t ≤ e ∧ e ≤ (D+1)*(t+D) := by
  let n := e+D
  let d := D+1
  let s := stepOne D e
  let t := e-D*s
  have hd : 0 < d := by dsimp [d]; omega
  have lo := Nat.lt_mul_div_succ n hd
  have hi := Nat.mul_div_le n d
  rw [Nat.mul_add, Nat.mul_one] at lo
  have hround : e ≤ d*s ∧ d*s ≤ e+d := by
    change e ≤ d * max 1 (n/d) ∧ d * max 1 (n/d) ≤ e+d
    by_cases h : 1 ≤ n/d
    · rw [Nat.max_eq_right h]; dsimp [n, d] at *; omega
    · rw [Nat.max_eq_left (by omega), Nat.mul_one]
      rw [Nat.eq_zero_of_not_pos h, Nat.mul_zero] at lo
      dsimp [n, d] at *
      omega
  obtain ⟨hl, hu⟩ := hround
  have hl' := Nat.mul_le_mul_left D hl
  have hu' := Nat.mul_le_mul_left D hu
  have hcomm : d*(D*s) = D*(d*s) := Nat.mul_left_comm d D s
  have ha : e ≤ D*s+t := by dsimp [t]; omega
  have hb := Nat.mul_le_mul_left d ha
  rw [Nat.mul_add, hcomm] at hb
  rw [Nat.mul_add] at hu'
  have hde : d*e = D*e+e := by simp [d,Nat.add_mul]
  rw [hde] at hb
  refine ⟨hl, hu, ?_, ?_⟩
  · change d*t ≤ e
    by_cases h : D*s ≤ e
    · have hsum : D*s+t = e := by dsimp [t]; omega
      have hh : d*(D*s+t) = d*e := congrArg (fun a => d*a) hsum
      rw [Nat.mul_add, hcomm, hde] at hh
      omega
    · have hz : t = 0 := by dsimp [t]; omega
      simp [hz]
  · change e ≤ d*(t+D)
    rw [Nat.mul_add, Nat.mul_comm d D]
    omega

theorem stepOne_sandwich (D : Nat) (ps : List (Nat × Nat))
    (hp : ∀ pe ∈ ps, 0 < pe.1) :
    let q := factorProduct id ps
    let m := factorProduct (fun _ => 1) ps
    let A := factorProduct (stepOne D) ps
    let qD := factorProduct (fun e => e-D*stepOne D e) ps
    A^(D+1) ≤ q*m^(D+1) ∧ qD^(D+1) ≤ q ∧ q ≤ (qD*m^D)^(D+1) := by
  dsimp only
  constructor
  · rw [← product_scale, ← product_scale, ← product_add]
    apply product_le_product _ _ _ ps hp
    intro e
    simpa using (stepOne_bounds D e).2.1
  constructor
  · rw [← product_scale]
    exact product_le_product _ _ (fun e => (stepOne_bounds D e).2.2.1) ps hp
  · rw [← product_scale (fun _ => 1) D, ← product_add, ← product_scale]
    apply product_le_product _ _ _ ps hp
    intro e
    simpa using (stepOne_bounds D e).2.2.2

open Lean.Grind Std

/-- Tail arithmetic for U ≥ 8 and D = ceil(3U/2), expressed using the
two defining inequalities for D. In an ordered field, dividing the first
three conclusions gives min(U/(D+1), 1−U/(D+1), D−U) ≥ 1/3;
the fourth gives D(D−1) ≤ (5/2)U². -/
theorem tail_ordered_ring {R : Type} [CommRing R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
    (u d : R) (h8 : 8 ≤ u) (hl : 3*u ≤ 2*d) (hu : 2*d < 3*u + 2) :
    d+1 ≤ 3*u ∧ 3*u ≤ 2*(d+1) ∧ 3*u+1 ≤ 3*d ∧ 2*d*(d-1) ≤ 5*u^2 := by
  have h13 : 8*d ≤ 13*u := by grind
  have h3 : 2*(d-1) ≤ 3*u := by grind
  have hnn : 0 ≤ 2*(d-1) := by grind
  have huu : 0 ≤ 13*u := by grind
  have hprod := OrderedRing.mul_le_mul_of_nonneg_right h13 hnn
  have hprod2 := OrderedRing.mul_le_mul_of_nonneg_left h3 huu
  have hpos := OrderedRing.mul_nonneg (show 0 ≤ u by grind) (show 0 ≤ u by grind)
  grind

section
variable {R : Type} [CommRing R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]

/-- The scalar absorption at the end of Proposition 3.2, after clearing
denominators: J S ≤ A(S+J), with A=4CW² and S=X^δ. -/
theorem gram_absorption (J S A : R) (hS : 0 < S) (hJ : 0 ≤ J)
    (hgap : 2*A ≤ S) (hgram : J*S ≤ A*(S+J)) : J ≤ 2*A := by
  have := OrderedRing.mul_le_mul_of_nonneg_right hgap hJ
  by_cases h : J ≤ 2*A
  · exact h
  · have ht : 2*A < J := by grind
    have := OrderedRing.mul_lt_mul_of_pos_right ht hS
    grind

/-- ∑ 2ʲ bⱼ for a list of nonnegative level-set masses. -/
def dyadicMass : List R → R
  | [] => 0
  | b::bs => b + 2*dyadicMass bs

/-- The jth entry b satisfies (scale · 4ʲ)b ≤ B. -/
def dyadicControl (B scale : R) : List R → Prop
  | [] => True
  | b::bs => scale*b ≤ B ∧ dyadicControl B (4*scale) bs

theorem dyadic_charge (B h : R) (hB : 0 ≤ B) (hh : 0 ≤ h) (bs : List R)
    (hc : dyadicControl B 1 bs) : (2*h)*dyadicMass bs ≤ (4*h)*B := by
  have aux : ∀ (xs : List R) (k : R), dyadicControl B k xs → k*dyadicMass xs ≤ 2*B := by
    intro xs
    induction xs with
    | nil =>
      intro k _
      simp only [dyadicMass]
      grind
    | cons b bs ih =>
      intro k hc
      obtain ⟨hb,ht⟩ := hc
      specialize ih (4*k) ht
      simp only [dyadicMass]
      grind
  have hs := aux bs 1 hc
  have h2 : dyadicMass bs ≤ 2*B := by grind
  have := OrderedRing.mul_le_mul_of_nonneg_left h2 hh
  grind

theorem short_degree (u d : R) (h1 : 1 ≤ u) (hl : 2*u ≤ d) (hu : d < 2*u+1) :
    d+1 ≤ 4*u ∧ 4*u ≤ 3*(d+1) ∧ 4*u+1 ≤ 4*d ∧ d*(d-1) ≤ 6*u^2 := by
  have h3 : d ≤ 3*u := by grind
  have h2 : d-1 ≤ 2*u := by grind
  have hnn : 0 ≤ d-1 := by grind
  have hnu : 0 ≤ 3*u := by grind
  have := OrderedRing.mul_le_mul_of_nonneg_right h3 hnn
  have := OrderedRing.mul_le_mul_of_nonneg_left h2 hnu
  grind
end

open Lean.Grind Std
section
variable {R : Type} [CommRing R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]

theorem normalized_denominator (u d mu a q : R) (hu : 1 < u) (hdlo : 4*u ≤ d)
    (hdhi : d < 4*u+1) (hA : (2*d+1)*a ≤ 2*u + (2*d+1)*mu)
    (hQL : u ≤ (2*d+1)*(q+d*mu)) (hQU : (2*d+1)*q ≤ u)
    (hsmall : 132*(d*mu) ≤ 1) (hm : 12*mu ≤ 1) :
    1 ≤ 12*q ∧ 7*q ≤ 1 ∧ 3*a ≤ 1 := by
  let F := 2*d+1
  have hF : 0 < F := by dsimp [F]; grind
  have hF0 : 0 ≤ F := by grind
  have hFs : F*(132*(d*mu)) ≤ F*1 := OrderedRing.mul_le_mul_of_nonneg_left hsmall hF0
  have hFm : F*(12*mu) ≤ F*1 := OrderedRing.mul_le_mul_of_nonneg_left hm hF0
  have hQ : 1 ≤ 12*q := by
    by_cases hh : 1 ≤ 12*q
    · exact hh
    · have hlt : 12*q < 1 := by grind
      have hhF := OrderedRing.mul_lt_mul_of_pos_left hlt hF
      dsimp [F] at hFs hhF
      grind
  have hQ' : 7*q ≤ 1 := by
    by_cases hh : 7*q ≤ 1
    · exact hh
    · have hlt : 1 < 7*q := by grind
      have hhF := OrderedRing.mul_lt_mul_of_pos_left hlt hF
      dsimp [F] at hhF
      grind
  have hA' : 3*a ≤ 1 := by
    by_cases hh : 3*a ≤ 1
    · exact hh
    · have hlt : 1 < 3*a := by grind
      have hhF := OrderedRing.mul_lt_mul_of_pos_left hlt hF
      dsimp [F] at hFm hhF
      grind
  exact ⟨hQ,hQ',hA'⟩
end

open Lean.Grind Std
section
variable {R : Type} [CommRing R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
theorem weyl_denominator (d M : R) (hM : 1 ≤ M) (hlo : 1 ≤ d) (hd : d ≤ 4*M+1) :
    12*d*(d-1) ≤ 300*M^2 := by
  have h5 : d ≤ 5*M := by grind
  have h4 : d-1 ≤ 5*M := by grind
  have h1 : 0 ≤ d-1 := by grind
  have h2 : 0 ≤ 5*M := by grind
  have := OrderedRing.mul_le_mul_of_nonneg_right h5 h1
  have := OrderedRing.mul_le_mul_of_nonneg_left h4 h2
  grind
end

theorem difference_modulus (q B h : Nat) (hq : 0 < q) :
    q / Nat.gcd (B*h) q =
      (q / Nat.gcd B q) / Nat.gcd h (q / Nat.gcd B q) := by
  let g := Nat.gcd B q
  let u := B / g
  let v := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right B hq
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have hB : g*u = B := Nat.mul_div_cancel' (Nat.gcd_dvd_left B q)
  have hq' : g*v = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right B q)
  have heq : Nat.gcd (B*h) q = g * Nat.gcd h v := by
    calc
      Nat.gcd (B*h) q = Nat.gcd (g*(u*h)) (g*v) := by rw [← Nat.mul_assoc, hB, hq']
      _ = g * Nat.gcd h v := by rw [Nat.gcd_mul_left, hcop.gcd_mul_left_cancel]
  change q / Nat.gcd (B*h) q = (q/g) / Nat.gcd h v
  rw [heq, Nat.div_div_eq_div_mul]

#print axioms ceiling_bounds
#print axioms exponent_bounds
#print axioms reduced_denominator
#print axioms reduced_denominator_for
#print axioms stepOne_bounds
#print axioms stepOne_sandwich
#print axioms tail_ordered_ring
#print axioms gram_absorption
#print axioms dyadic_charge
#print axioms short_degree
#print axioms normalized_denominator
#print axioms weyl_denominator
#print axioms difference_modulus
#print axioms degree_drop
#print axioms denominator_sandwich

end WaringLinear
