import WaringSiegel.WSL2MomentDivisorBridge

/-!
# The literal off-diagonal substitution in the mixed sixth moment

After ordinary congruence modulo `m^3` has been obtained by kernel averaging,
the variables are changed to `h = (x₂-x₁)/m^3` and `z = x₁+x₂`.  The quotient
here is an actual ring element selected from the divisibility witness.  Its
equation, uniqueness, nonvanishing, exact transformed equation, injectivity,
and number-field archimedean ranges are proved below.
-/

noncomputable section
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL2

section Algebra
variable {R : Type*} [CommRing R]

def cubicCongruenceQuotient (m x y : R) : R :=
  if h : m^3 ∣ y-x then h.choose else 0

theorem cubicCongruenceQuotient_mul (m x y : R) (h : m^3 ∣ y-x) :
    m^3*cubicCongruenceQuotient m x y = y-x := by
  simp only [cubicCongruenceQuotient, dif_pos h]
  exact h.choose_spec.symm

def cubicOffdiagonalCoordinates (m : R) (p : R×R) : R×R :=
  (cubicCongruenceQuotient m p.1 p.2, p.1+p.2)

theorem four_mul_cube_difference (x y : R) :
    4*(y^3-x^3) = (y-x)*(3*(x+y)^2+(y-x)^2) := by ring

theorem cubic_transformation_identity (m x y : R) (h : m^3 ∣ y-x) :
    m^3 * (cubicCongruenceQuotient m x y *
      (3*(x+y)^2+(cubicCongruenceQuotient m x y)^2*m^6)) = 4*(y^3-x^3) := by
  calc
    _ = (m^3*cubicCongruenceQuotient m x y) *
        (3*(x+y)^2+(m^3*cubicCongruenceQuotient m x y)^2) := by ring
    _ = (y-x)*(3*(x+y)^2+(y-x)^2) := by rw [cubicCongruenceQuotient_mul m x y h]
    _ = _ := (four_mul_cube_difference x y).symm

theorem cubicCongruenceQuotient_ne_zero (m x y : R) (h : m^3 ∣ y-x) (hxy : x≠y) :
    cubicCongruenceQuotient m x y ≠ 0 := by
  intro hz
  have hdiff := cubicCongruenceQuotient_mul m x y h
  rw [hz, mul_zero] at hdiff
  exact hxy (sub_eq_zero.mp hdiff.symm).symm

variable [IsDomain R] [CharZero R]

theorem cubicCongruenceQuotient_unique (m x y h : R) (hm : m≠0)
    (hh : m^3*h=y-x) : cubicCongruenceQuotient m x y=h := by
  apply mul_left_cancel₀ (pow_ne_zero 3 hm)
  exact (cubicCongruenceQuotient_mul m x y ⟨h,hh.symm⟩).trans hh.symm

theorem cubicOffdiagonalCoordinates_injOn (m : R) :
    Set.InjOn (cubicOffdiagonalCoordinates m) {p : R×R | m^3 ∣ p.2-p.1} := by
  intro p hp q hq heq
  have hfirst : cubicCongruenceQuotient m p.1 p.2 = cubicCongruenceQuotient m q.1 q.2 :=
    congrArg Prod.fst heq
  have hsum : p.1+p.2=q.1+q.2 := congrArg Prod.snd heq
  have hdiff : p.2-p.1=q.2-q.1 := by
    rw [← cubicCongruenceQuotient_mul m p.1 p.2 hp,
      ← cubicCongruenceQuotient_mul m q.1 q.2 hq, hfirst]
  have htwice : (2:R)*p.1=2*q.1 := by
    calc
      _ = (p.1+p.2)-(p.2-p.1) := by ring
      _ = (q.1+q.2)-(q.2-q.1) := by rw [hsum,hdiff]
      _ = _ := by ring
  have hpq : p.1=q.1 := mul_left_cancel₀ (two_ne_zero : (2:R)≠0) htwice
  apply Prod.ext hpq
  simpa only [hpq, add_left_cancel_iff] using hsum

/-- The exact quadratic/sixth-power equation, in both directions. -/
theorem mixed_cubic_transformed_iff (m x y A B : R) (hm : m≠0) (h : m^3 ∣ y-x) :
    (x^3+m^3*A=y^3+m^3*B) ↔
      cubicCongruenceQuotient m x y *
        (3*(x+y)^2+(cubicCongruenceQuotient m x y)^2*m^6) = 4*(A-B) := by
  have hid := cubic_transformation_identity m x y h
  constructor
  · intro heq
    have hdiff : m^3*(A-B)=y^3-x^3 := by
      calc
        _ = (x^3+m^3*A)-(x^3+m^3*B) := by ring
        _ = (y^3+m^3*B)-(x^3+m^3*B) := by rw [heq]
        _ = _ := by ring
    apply mul_left_cancel₀ (pow_ne_zero 3 hm)
    calc
      _ = 4*(y^3-x^3) := hid
      _ = 4*(m^3*(A-B)) := by rw [hdiff]
      _ = _ := by ring
  · intro heq
    have hdiff : y^3-x^3=m^3*(A-B) := by
      apply mul_left_cancel₀ (by norm_num : (4:R)≠0)
      calc
        _ = m^3 * (cubicCongruenceQuotient m x y *
            (3*(x+y)^2+(cubicCongruenceQuotient m x y)^2*m^6)) := hid.symm
        _ = m^3*(4*(A-B)) := by rw [heq]
        _ = _ := by ring
    calc
      _ = x^3+m^3*(A-B)+m^3*B := by ring
      _ = x^3+(y^3-x^3)+m^3*B := by rw [hdiff]
      _ = _ := by ring

def mixedCubicOffdiagonalPairs (X : Finset R) (m A B : R) : Finset (R×R) :=
  (X.product X).filter (fun p => p.1≠p.2 ∧ m^3 ∣ p.2-p.1 ∧
    p.1^3+m^3*A=p.2^3+m^3*B)

def mixedTransformedPairs (H Z : Finset R) (m A B : R) : Finset (R×R) :=
  (H.product Z).filter (fun p => p.1≠0 ∧ p.1*(3*p.2^2+p.1^2*m^6)=4*(A-B))

/-- Dropping the parity/recovery restrictions can only enlarge the actual
finite transformed solution count. -/
theorem mixed_offdiagonal_pair_count_le (X H Z : Finset R) (m A B : R) (hm : m≠0)
    (hH : ∀x∈X, ∀y∈X, x≠y → m^3 ∣ y-x → cubicCongruenceQuotient m x y∈H)
    (hZ : ∀x∈X, ∀y∈X, x+y∈Z) :
    (mixedCubicOffdiagonalPairs X m A B).card ≤ (mixedTransformedPairs H Z m A B).card := by
  apply Finset.card_le_card_of_injOn (cubicOffdiagonalCoordinates m)
  · intro p hp
    obtain ⟨hpmem,hpne,hpdiv,hpeq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hpmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hH p.1 hx p.2 hy hpne hpdiv,hZ p.1 hx p.2 hy⟩, ?_, ?_⟩
    · exact cubicCongruenceQuotient_ne_zero m p.1 p.2 hpdiv hpne
    · exact (mixed_cubic_transformed_iff m p.1 p.2 A B hm hpdiv).mp hpeq
  · intro p hp q hq heq
    exact cubicOffdiagonalCoordinates_injOn m (Finset.mem_filter.mp hp).2.2.1
      (Finset.mem_filter.mp hq).2.2.1 heq

end Algebra

section NumberField
variable {K : Type*} [Field K] [NumberField K]

theorem cubicCongruenceQuotient_place_bound (m x y : 𝓞 K) (hc : m^3 ∣ y-x)
    (P M : ℝ) (hM : 0<M)
    (hm : ∀v : NumberField.InfinitePlace K, M≤v (m:K))
    (hx : ∀v : NumberField.InfinitePlace K, v (x:K)≤P)
    (hy : ∀v : NumberField.InfinitePlace K, v (y:K)≤P)
    (v : NumberField.InfinitePlace K) :
    v ((cubicCongruenceQuotient m x y : 𝓞 K) : K) ≤ 2*P/M^3 := by
  have hmul := congrArg (fun z : 𝓞 K => v (z:K)) (cubicCongruenceQuotient_mul m x y hc)
  change v ((m:K)^3*((cubicCongruenceQuotient m x y : 𝓞 K) : K)) = v ((y-x : 𝓞 K):K) at hmul
  rw [map_mul,map_pow] at hmul
  apply (le_div_iff₀ (pow_pos hM 3)).mpr
  calc
    _ ≤ v ((cubicCongruenceQuotient m x y : 𝓞 K) : K) * v (m:K)^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le (hm v) 3)
        (apply_nonneg v _)
    _ = v ((y-x : 𝓞 K):K) := by simpa only [mul_comm] using hmul
    _ ≤ 2*P := place_sub_le_twice hy hx v

theorem cubic_sum_place_bound (x y : 𝓞 K) (P : ℝ)
    (hx : ∀v : NumberField.InfinitePlace K, v (x:K)≤P)
    (hy : ∀v : NumberField.InfinitePlace K, v (y:K)≤P)
    (v : NumberField.InfinitePlace K) : v ((x+y : 𝓞 K):K)≤2*P := by
  change v ((x:K)+(y:K))≤2*P
  have hb := v.val.add_le (x:K) (y:K)
  change v ((x:K)+(y:K)) ≤ v (x:K)+v (y:K) at hb
  exact hb.trans (by linarith [hx v,hy v])

end NumberField
end WaringSiegel.WSL2
