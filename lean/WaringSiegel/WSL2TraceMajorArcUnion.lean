import WaringSiegel.WSL2TraceMajorArcs
import WaringSiegel.WSL2TraceKernel

/-!
# WSL2: finite rational center classes and the full trace major-arc set

Bounded conductor norm gives finitely many actual rational classes in V/D⁻¹.
The proof places each class in the kernel of multiplication by the positive
integer norm of its conductor. Consequently the full union over every field
center is a finite union of compact arcs, without choosing a lattice window.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorusMul_traceRationalPoint (a : 𝓞 K) (γ : K) :
    traceTorusMul a (traceRationalPoint γ) = traceRationalPoint ((a : K) * γ) := by
  simp only [traceRationalPoint, traceTorusMul_mk, map_mul]

theorem traceConductor_norm_annihilates (γ : K) :
    traceRationalPoint γ ∈
      (traceTorusMul (Ideal.absNorm (traceConductor γ) : 𝓞 K)).ker := by
  rw [AddMonoidHom.mem_ker, traceTorusMul_traceRationalPoint]
  change Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero, mem_archInverseDifferentLattice]
  refine ⟨((Ideal.absNorm (traceConductor γ) : 𝓞 K) : K) * γ, ?_, rfl⟩
  exact Ideal.absNorm_mem (traceConductor γ)

/-- Distinct field representatives of one trace class have the same conductor. -/
theorem traceConductor_eq_of_point_eq (γ δ : K)
    (h : traceRationalPoint γ = traceRationalPoint δ) :
    traceConductor γ = traceConductor δ := by
  have hd := (traceRationalPoint_eq_iff γ δ).mp h
  have he : γ = δ + (γ - δ) := by ring
  conv_lhs => rw [he]
  exact conductorIdeal_add_lattice _ _ _ hd

def traceRationalCenters (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    Set (ArchimedeanTraceTorus K) :=
  {q | ∃ γ : K, traceRationalPoint γ = q ∧ Ideal.absNorm (traceConductor γ) ≤ N}

theorem traceRationalCenters_finite (N : ℕ) : (traceRationalCenters K N).Finite := by
  have hfin : (⋃ n ∈ Set.Icc 1 N,
      ((traceTorusMul (n : 𝓞 K)).ker : Set (ArchimedeanTraceTorus K))).Finite := by
    apply (Set.finite_Icc 1 N).biUnion
    intro n hn
    apply traceTorusMul_kernel_finite
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn.1))
  apply hfin.subset
  rintro q ⟨γ, rfl, hγ⟩
  refine Set.mem_iUnion₂.mpr ⟨Ideal.absNorm (traceConductor γ), ⟨?_, hγ⟩, ?_⟩
  · exact conductorIdeal_absNorm_pos _ inverseDifferent_ne_zero γ
  · exact traceConductor_norm_annihilates γ

instance traceRationalCenters_finite_type (N : ℕ) : Finite (traceRationalCenters K N) :=
  (traceRationalCenters_finite (K := K) N).to_subtype

def traceCenterRepresentative {N : ℕ} (q : traceRationalCenters K N) : K :=
  q.property.choose

theorem traceCenterRepresentative_spec {N : ℕ} (q : traceRationalCenters K N) :
    traceRationalPoint (traceCenterRepresentative q) = q ∧
      Ideal.absNorm (traceConductor (traceCenterRepresentative q)) ≤ N :=
  q.property.choose_spec

theorem traceMajorArc_eq_of_point_eq (H L : ℝ) (γ δ : K)
    (h : traceRationalPoint γ = traceRationalPoint δ) :
    traceMajorArc H L γ = traceMajorArc H L δ := by
  have hd := (traceRationalPoint_eq_iff γ δ).mp h
  have he : γ = δ + (γ - δ) := by ring
  conv_lhs => rw [he]
  exact traceMajorArc_add_inverseDifferent H L δ (γ-δ) hd

theorem traceConductor_norm_le_of_mem_traceMajorArc (H L : ℝ) (γ : K)
    {q : ArchimedeanTraceTorus K} (hq : q ∈ traceMajorArc H L γ) :
    (Ideal.absNorm (traceConductor γ) : ℝ) ≤ L := by
  obtain ⟨x, hx, _⟩ := hq
  exact (le_mul_of_one_le_right (Nat.cast_nonneg _)
    (productArcWeight_one_le H (x - mixedEmbedding K γ))).trans hx

/-- The full major-arc union, over every rational field center. -/
def traceMajorArcUnion (H L : ℝ) : Set (ArchimedeanTraceTorus K) :=
  ⋃ γ : K, traceMajorArc H L γ

/-- The full union equals a finite union indexed by genuine trace classes
with conductor norm at most floor(L). -/
theorem traceMajorArcUnion_eq_finite_union (H L : ℝ) :
    traceMajorArcUnion (K := K) H L =
      ⋃ q : traceRationalCenters K ⌊L⌋₊, traceMajorArc H L (traceCenterRepresentative q) := by
  ext θ
  constructor
  · intro hθ
    obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hθ
    have hN : Ideal.absNorm (traceConductor γ) ≤ ⌊L⌋₊ :=
      Nat.le_floor (traceConductor_norm_le_of_mem_traceMajorArc H L γ hγ)
    let q : traceRationalCenters K ⌊L⌋₊ := ⟨traceRationalPoint γ, γ, rfl, hN⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    rw [traceMajorArc_eq_of_point_eq H L (traceCenterRepresentative q) γ
      (traceCenterRepresentative_spec q).1]
    exact hγ
  · intro hθ
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hθ
    exact Set.mem_iUnion.mpr ⟨traceCenterRepresentative q, hq⟩

theorem traceMajorArcUnion_isCompact (H L : ℝ) (hH : 0 < H) :
    IsCompact (traceMajorArcUnion (K := K) H L) := by
  rw [traceMajorArcUnion_eq_finite_union]
  exact isCompact_iUnion (fun q => traceMajorArc_isCompact H L hH (traceCenterRepresentative q))

theorem traceMajorArcUnion_measurableSet (H L : ℝ) (hH : 0 < H) :
    MeasurableSet (traceMajorArcUnion (K := K) H L) :=
  (traceMajorArcUnion_isCompact H L hH).isClosed.measurableSet

theorem traceMajorArcUnion_pairwise_disjoint (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K) :
    Pairwise (fun (q r : traceRationalCenters K ⌊L⌋₊) =>
      Disjoint (traceMajorArc H L (traceCenterRepresentative q))
        (traceMajorArc H L (traceCenterRepresentative r))) := by
  intro q r hqr
  apply traceMajorArcs_disjoint H L hH hL hsmall
  rw [(traceCenterRepresentative_spec q).1, (traceCenterRepresentative_spec r).1]
  exact fun h => hqr (Subtype.ext h)

end WaringSiegel
