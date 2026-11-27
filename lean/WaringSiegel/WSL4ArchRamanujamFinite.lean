import WaringSiegel.WSL4ArchRamanujamIdeal

/-! # Exactly s+1 coordinates for the truncated power expressions -/
noncomputable section
open scoped BigOperators
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

def ramanujamPowerTuple (p s : ℕ) {R : Type*} [CommRing R] (x : Fin (s+1) → R) : R :=
  ∑i : Fin (s+1),(p:R)^i.val*x i^(p^(s-i.val))

def ramanujamExtendTuple {s : ℕ} (x : Fin (s+1) → R) (i : ℕ) : R :=
  if h : i<s+1 then x ⟨i,h⟩ else 0

theorem ramanujamPowerTuple_restrict (s : ℕ) (x : ℕ → R) :
    ramanujamPowerTuple p s (fun i => x i)=ramanujamPowerSum p s x :=
  Fin.sum_univ_eq_sum_range (fun i => (p:R)^i*x i^(p^(s-i))) (s+1)

theorem ramanujamPowerSum_extend (s : ℕ) (x : Fin (s+1) → R) :
    ramanujamPowerSum p s (ramanujamExtendTuple x)=ramanujamPowerTuple p s x := by
  rw [← ramanujamPowerTuple_restrict]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ramanujamExtendTuple,dif_pos i.isLt,Fin.eta]

theorem mem_ramanujamPowerSubring_iff_fin (s : ℕ) (a : R) :
    a∈ramanujamPowerSubring p s R ↔
      ∃x : Fin (s+1) → R,ramanujamPowerTuple p s x=a := by
  rw [mem_ramanujamPowerSubring_iff]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨fun i => x i,(ramanujamPowerTuple_restrict s x).trans hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨ramanujamExtendTuple x,(ramanujamPowerSum_extend s x).trans hx⟩

theorem mem_ramanujamPowerIdeal_iff_fin (s : ℕ) (I : Ideal R)
    (a : ramanujamPowerSubring p s R) :
    a∈ramanujamPowerIdeal p s I ↔
      ∃x : Fin (s+1) → R,(∀i,x i∈I) ∧ ramanujamPowerTuple p s x=(a:R) := by
  rw [mem_ramanujamPowerIdeal_iff]
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨fun i => x i,fun i => hx i,(ramanujamPowerTuple_restrict s x).trans he⟩
  · rintro ⟨x,hx,he⟩
    refine ⟨ramanujamExtendTuple x,?_,(ramanujamPowerSum_extend s x).trans he⟩
    intro i
    by_cases hi : i<s+1
    · simpa only [ramanujamExtendTuple,dif_pos hi] using hx ⟨i,hi⟩
    · simpa only [ramanujamExtendTuple,dif_neg hi] using I.zero_mem

theorem ramanujamPowerTuple_add (s : ℕ) (x y : Fin (s+1) → R) :
    ∃z : Fin (s+1) → R,
      ramanujamPowerTuple p s z=ramanujamPowerTuple p s x+ramanujamPowerTuple p s y :=
  (mem_ramanujamPowerSubring_iff_fin s _).mp
    ((ramanujamPowerSubring p s R).add_mem
      ((mem_ramanujamPowerSubring_iff_fin s _).mpr ⟨x,rfl⟩)
      ((mem_ramanujamPowerSubring_iff_fin s _).mpr ⟨y,rfl⟩))

theorem ramanujamPowerTuple_mul (s : ℕ) (x y : Fin (s+1) → R) :
    ∃z : Fin (s+1) → R,
      ramanujamPowerTuple p s z=ramanujamPowerTuple p s x*ramanujamPowerTuple p s y :=
  (mem_ramanujamPowerSubring_iff_fin s _).mp
    ((ramanujamPowerSubring p s R).mul_mem
      ((mem_ramanujamPowerSubring_iff_fin s _).mpr ⟨x,rfl⟩)
      ((mem_ramanujamPowerSubring_iff_fin s _).mpr ⟨y,rfl⟩))

theorem prime_power_difference_finite_ideal_expression
    (s : ℕ) (I : Ideal R) (x y : R) (hxy : x-y∈I) :
    ∃z : Fin (s+1) → R,(∀i,z i∈I) ∧ ramanujamPowerTuple p s z=x^(p^s)-y^(p^s) := by
  obtain ⟨z,hz,he⟩ := prime_power_difference_truncated_ideal_expression (p:=p) s I x y hxy
  exact ⟨fun i => z i,fun i => hz i,(ramanujamPowerTuple_restrict s z).trans he⟩

#print axioms mem_ramanujamPowerSubring_iff_fin
#print axioms mem_ramanujamPowerIdeal_iff_fin
#print axioms ramanujamPowerTuple_add
#print axioms ramanujamPowerTuple_mul
#print axioms prime_power_difference_finite_ideal_expression
end WaringSiegel.WSL4
