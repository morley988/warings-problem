import Std

/-! Exact positive-rational certificates for the finite-degree moment iteration.
The analytic inputs are identified by degree and order in the accompanying paper.
The statements here record deductions in the arithmetic of admissible excesses. -/
namespace WaringSmall

/-- A nonnegative fraction, stored without gcd reduction. All public numerical
rules check the denominators of their input data. -/
structure Fr where
  n : Nat
  d : Nat
deriving DecidableEq, Repr
def whole (n : Nat) : Fr := ⟨n,1⟩
def valid (q : Fr) : Bool := 0 < q.d
def le (a b : Fr) : Bool := a.n*b.d ≤ b.n*a.d
def lt (a b : Fr) : Bool := a.n*b.d < b.n*a.d
def eq (a b : Fr) : Bool := a.n*b.d = b.n*a.d
def plus (a b : Fr) : Fr := ⟨a.n*b.d+b.n*a.d,a.d*b.d⟩
def times (a b : Fr) : Fr := ⟨a.n*b.n,a.d*b.d⟩
def minus (a b : Fr) : Fr := ⟨a.n*b.d-b.n*a.d,a.d*b.d⟩
def divNat (a : Fr) (b : Nat) : Fr := ⟨a.n,a.d*b⟩
def one := whole 1

/-- Extend the certified conductor interval. All endpoints share denominator
`den`, including the scaled quantities `theta` and `sigma`. -/
def addInterval (den theta sigma endpoint j : Nat) : Nat :=
  let y := 2^j * sigma
  let left := j*theta + 2*y
  let right := (j+2)*den - (2^(j+2)-2)*sigma
  if 2*y ≤ den && (j=0 || theta+y ≤ den) &&
     left ≤ endpoint && endpoint ≤ right then right else endpoint

def conduct (k : Nat) (m z sigma : Fr) : Bool :=
  let d := m.d*k*10^6
  let den := d*sigma.d
  let theta := (m.n*10^6+m.d*k)*sigma.d
  let endp := (List.range (k-1)).foldl (addInterval den theta (sigma.n*d)) den
  valid m && valid z && valid sigma && 2 ≤ k && 0 < z.n &&
  lt (times (whole 2) z) sigma && lt m (whole k) && m.n*den < endp*m.d

def interpolateOK (u d lo a hi b : Fr) : Bool :=
  valid u && valid d && lt lo hi && le lo u && le u hi &&
  le (plus (times (minus hi u) a) (times (minus u lo) b)) (times (minus hi lo) d)

def stepOK (k : Nat) (u d prior a h b L M z : Fr) : Bool :=
  valid u && valid d && valid L && 0 < L.n && lt L M &&
  le (whole (k+2)) u && eq (plus prior (whole 2)) u && lt h u &&
  le (times (whole k) a) (plus (times (whole k) d) (times L a)) &&
  le (plus b (times h z)) (plus d (times u z))

/-- The inductive closure of the printed seed table under interpolation and
the large-values step. A proof keeps the dependency tree of every bound. -/
inductive Derivation (k : Nat) (seeds : List (Fr × Fr)) : Fr → Fr → Prop
  | seed (u d : Fr) (h : (seeds.contains (u,d) && valid u && valid d)=true) :
      Derivation k seeds u d
  | interpolate {l a h b : Fr} (u d : Fr) (hl : Derivation k seeds l a)
      (hh : Derivation k seeds h b) (valid : interpolateOK u d l a h b=true) :
      Derivation k seeds u d
  | step {p a h b : Fr} (u d L M z sig : Fr) (hp : Derivation k seeds p a)
      (hh : Derivation k seeds h b) (hc : conduct k M z sig=true)
      (valid : stepOK k u d p a h b L M z=true) : Derivation k seeds u d

/-- Conditions for the final Holder split at the ordinary moment w=k(k+1).
The first equality specifies its restricted moment order r; the second
specifies the positive saving g=(a-(w-a)D)/w. -/
def outcomeOK (k s a cutoff : Nat) (r D gap : Fr) : Bool :=
  let b := s-a
  let w := k*(k+1)
  a<s && a<w && 4*k ≤ s && b<cutoff && a*cutoff ≥ (k+2)*(cutoff-b) &&
  valid gap && 0 < gap.n &&
  eq (times r (whole (w-a))) (whole (b*w)) &&
  eq (plus (times (whole w) gap) (times (whole (w-a)) D)) (whole a)

def Outcome (k s a cutoff : Nat) (seeds : List (Fr × Fr)) (gap : Fr) : Prop :=
  ∃ r d, Derivation k seeds r d ∧ outcomeOK k s a cutoff r d gap=true

/-- Exact sufficient inequality for the terminal zero-excess seeds at 17--20. -/
def terminalOK (k source cutoff : Nat) (d : Fr) : Bool :=
  let w := k*(k+1)
  source<cutoff && cutoff<w && valid d &&
  lt (times (whole (w-cutoff)) d) (whole (cutoff-source))
end WaringSmall
