import Std
import WaringEnvelope.Check

/-! # Arithmetic exponent-pair words

A pair records κ, λ and the radical loss D as nonnegative rational numbers.
The evaluation starts from (1/2,1/2,1/2). Each word also carries the
nonvanishing test for the degree exponents of the successive local phases.
-/
namespace WaringDualEnvelope

structure Pair where
  x : Nat
  y : Nat
  denominator : Nat
  loss : Nat
  lossDen : Nat
deriving DecidableEq, Repr

/-- Common denominator for the exponents, separate denominator for the loss. -/
def normalized (x y d l e : Nat) : Pair :=
  let g := Nat.gcd x (Nat.gcd y d)
  let h := Nat.gcd l e
  ⟨x/g,y/g,d/g,l/h,e/h⟩

def basePair : Pair := ⟨1,1,2,1,2⟩

def pairStep (p : Pair) (Bmove : Bool) : Pair :=
  if Bmove then
    normalized (2*p.y-p.denominator) (2*p.x+p.denominator) (2*p.denominator)
      (2*p.loss*p.denominator + p.lossDen*p.denominator + 2*p.lossDen*p.y)
      (2*p.lossDen*p.denominator)
  else
    normalized p.x (p.x+p.y+p.denominator) (2*p.denominator+2*p.x)
      (p.loss+p.lossDen) (2*p.lossDen)

def pairOfWord (w : List Bool) : Pair := w.foldl pairStep basePair

/-- Affine form a*k+b in the positive integer degree k. -/
abbrev Affine := Int × Int

def evalAffine (a : Affine) (k : Nat) : Int := a.1*k+a.2

def avoidsZero (a : Affine) : Bool :=
  if a.1=0 then a.2 != 0 else (-a.2)%a.1 != 0 || (-a.2)/a.1 < 21

def subForm (a b : Affine) : Affine := (a.1-b.1,a.2-b.2)

def avoidsPoles (den num : Affine) (w : List Bool) : Bool :=
  let diff := subForm num den
  let ok := avoidsZero den && avoidsZero num && avoidsZero diff
  match w with
  | [] => ok
  | op :: rest => ok && (if op then avoidsPoles diff num rest else avoidsPoles den diff rest)

def validWord (w : List Bool) : Bool := avoidsPoles (0,1) (1,0) w.reverse

theorem avoidsZero_sound {a : Affine} (h : avoidsZero a = true) {k : Nat} (hk : 21≤k) :
    evalAffine a k ≠ 0 := by
  rcases a with ⟨s,b⟩
  simp only [avoidsZero,evalAffine] at *
  intro hn
  by_cases hs : s=0
  · simp [hs] at hn h
    exact h hn
  · have heq : -b=s*k := by omega
    simp [hs, heq] at h
    omega

/-- All tested numerators, denominators and differences are nonzero for every
k≥21, with the actual A and B transformations on their affine forms. -/
inductive SafeAt (k : Nat) : Affine → Affine → List Bool → Prop
  | nil : evalAffine d k ≠ 0 → evalAffine e k ≠ 0 → evalAffine (subForm e d) k ≠ 0 →
      SafeAt k d e []
  | aStep : evalAffine d k ≠ 0 → evalAffine e k ≠ 0 → evalAffine (subForm e d) k ≠ 0 →
      SafeAt k d (subForm e d) xs → SafeAt k d e (false::xs)
  | bStep : evalAffine d k ≠ 0 → evalAffine e k ≠ 0 → evalAffine (subForm e d) k ≠ 0 →
      SafeAt k (subForm e d) e xs → SafeAt k d e (true::xs)

theorem avoidsPoles_sound (w : List Bool) (d e : Affine)
    (h : avoidsPoles d e w = true) (k : Nat) (hk : 21≤k) : SafeAt k d e w := by
  induction w generalizing d e with
  | nil =>
    simp only [avoidsPoles,Bool.and_eq_true] at h
    exact .nil (avoidsZero_sound h.1.1 hk) (avoidsZero_sound h.1.2 hk) (avoidsZero_sound h.2 hk)
  | cons op xs ih =>
    cases op <;> simp only [avoidsPoles,Bool.false_eq_true,if_false,if_true,Bool.and_eq_true] at h
    · exact .aStep (avoidsZero_sound h.1.1.1 hk) (avoidsZero_sound h.1.1.2 hk)
        (avoidsZero_sound h.1.2 hk) (ih _ _ h.2)
    · exact .bStep (avoidsZero_sound h.1.1.1 hk) (avoidsZero_sound h.1.1.2 hk)
        (avoidsZero_sound h.1.2 hk) (ih _ _ h.2)

end WaringDualEnvelope
