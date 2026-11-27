import WaringSiegel.WSL3MomentSparseGrowth
import WaringSiegel.WSL3MomentCritical

/-!
# A genuine number-field sparse critical VMVT

For every 1 <= r <= k, the system {t,...,t^(r-1),t^k} has critical
weighted moment of order r(r+1), with only X^epsilon beyond its exact L2
mass. The prime, quotient maps, annulus partition, Taylor normalization,
native congruence bound, and depth choices are all proved.
-/

noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators Classical NumberField WithZero

namespace WaringSiegel.WSL3
open WSL2

variable {K : Type*} [Field K] [NumberField K]

theorem numberField_sparse_critical_energy_bound (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α]
      (nodes : α → 𝓞 K), Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℝ, (∀ x, 0 ≤ w x) →
      weightedSystemEnergy (wooleyTriangular r) (fun x => sparseValue k r (nodes x)) w ≤
        C*(P^Module.finrank ℚ K : ℝ)^ε*(∑ x, w x^2)^wooleyTriangular r := by
  obtain ⟨p,hp,hkp,v,hnorm,hval⟩ := exists_large_unramified_degreeOne_prime (K := K) k
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨τ,δ,D,hτ,hδ,hD,hparams⟩ := sparse_partition_epsilon_parameters p r hp.one_lt hr hε
  obtain ⟨A,hA,B0,hmain⟩ := native_sparse_modular_energy_bound k r p hp hr hrk hkp hτ hδ
  let d := Module.finrank ℚ K
  let T : ℝ := (p : ℝ)^(B0+1)*(2 : ℝ)^d
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨A*D*T^ε,by positivity,?_⟩
  intro P hP α inst nodes hinj hbox w hw
  have hP0 : 0 ≤ P := by linarith
  have hX0 : 1 ≤ (2*P)^d := one_le_pow₀ (by linarith)
  obtain ⟨H,hHB,hHlo,hHhi⟩ := exists_depth_with_power_control p B0 hp.one_lt ((2*P)^d) hX0
  obtain ⟨c,hc,hcscale,hgrowth⟩ := hparams H
  let L := r*H+k*(H+c)
  let e := degreeOne_primePower_quotient_equiv v p hp hnorm hval L
  let f := degreeOne_primePower_quotient_equiv v p hp hnorm hval H
  let labels : α → ℤ := fun x => quotientIntegerRepresentative (v.asIdeal^L) e (nodes x)
  have hHL : H ≤ L := by dsimp [L]; nlinarith
  have hIJ : v.asIdeal^L ≤ v.asIdeal^H := Ideal.pow_le_pow_right hHL
  have hdeep : (2*P)^Module.finrank ℚ K < (Ideal.absNorm (v.asIdeal^H) : ℝ) := by
    simpa only [map_pow,hnorm,Nat.cast_pow] using hHlo
  have hlabels : Function.Injective (fun x => (labels x : ZMod (p^H))) :=
    integer_representatives_lower_residue_injective _ _ hIJ e f P hP0 hdeep nodes hinj hbox
  have heq : ∀ x y : Fin (wooleyTriangular r) → α,
      (∑ i, sparseValue k r (nodes (x i))) = (∑ i, sparseValue k r (nodes (y i))) →
      (∑ i, sparseValue k r (labels (x i) : ZMod (p^L))) =
        (∑ i, sparseValue k r (labels (y i) : ZMod (p^L))) := by
    intro x y hh
    funext j
    let g : 𝓞 K →+* ZMod (p^L) := e.toRingHom.comp (Ideal.Quotient.mk (v.asIdeal^L))
    have hhj : (∑ i, nodes (x i)^sparseDegree k r j) = ∑ i, nodes (y i)^sparseDegree k r j := by
      simpa only [Finset.sum_apply,sparseValue] using congrFun hh j
    have h := congrArg g hhj
    simpa only [map_sum,map_pow,g,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,
      Finset.sum_apply,sparseValue,labels,quotientIntegerRepresentative_cast] using h
  have hB : B0 ≤ r*H := hHB.trans (by nlinarith)
  have hbound := hmain H c L hB hc hcscale le_rfl labels hlabels w hw
  have hbase : (p : ℝ)^H ≤ T*P^d := by
    simpa only [T,mul_pow,mul_assoc] using hHhi
  have hpow : ((p : ℝ)^H)^ε ≤ T^ε*(P^d : ℝ)^ε := by
    rw [← Real.mul_rpow hT.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hbase hε.le
  calc
    weightedSystemEnergy (wooleyTriangular r) (fun x => sparseValue k r (nodes x)) w ≤
        weightedSystemEnergy (wooleyTriangular r) (fun x => sparseValue k r (labels x : ZMod (p^L))) w :=
      weightedSystemEnergy_le_of_equations _ _ _ heq w hw
    _ ≤ A*(1+(H : ℝ)*(p : ℝ)^c)^(2*wooleyTriangular r)*
        (p^(r*H) : ℝ)^δ*(∑ x, w x^2)^wooleyTriangular r := hbound
    _ = A*((1+(H : ℝ)*(p : ℝ)^c)^(2*wooleyTriangular r)*(p^(r*H) : ℝ)^δ)*
        (∑ x, w x^2)^wooleyTriangular r := by ring
    _ ≤ A*(D*((p : ℝ)^H)^ε)*(∑ x, w x^2)^wooleyTriangular r := by gcongr
    _ ≤ A*(D*(T^ε*(P^d : ℝ)^ε))*(∑ x, w x^2)^wooleyTriangular r := by gcongr
    _ = _ := by ring

/-- The sparse Wronskian system needed for generalized Hua, with arbitrary
complex coefficients and the exact L2 mass. -/
theorem numberField_sparse_critical_L2_moment_bound (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α]
      (nodes : α → 𝓞 K), Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ,
      (∫ θ, ‖frequencySum
        (fun x (ji : Fin r × NumberFieldCoordinateIndex K) =>
          integerCoordinates K (nodes x ^ sparseDegree k r ji.1) ji.2) w θ‖^(2*wooleyTriangular r)
        ∂latticeHaar) ≤ C*(P^Module.finrank ℚ K : ℝ)^ε*(∑ x, ‖w x‖^2)^wooleyTriangular r := by
  obtain ⟨C,hC,hmain⟩ := numberField_sparse_critical_energy_bound (K := K) k r hr hrk hε
  refine ⟨C,hC,?_⟩
  intro P hP α inst nodes hinj hbox w
  exact (system_moment_le_norm_weighted_energy (integerCoordinates K)
    (integerCoordinates_injective K) r (wooleyTriangular r)
    (fun x => sparseValue k r (nodes x)) w).trans
      (hmain P hP nodes hinj hbox (fun x => ‖w x‖) (fun _ => norm_nonneg _))

#print axioms numberField_sparse_critical_energy_bound
#print axioms numberField_sparse_critical_L2_moment_bound

end WaringSiegel.WSL3
