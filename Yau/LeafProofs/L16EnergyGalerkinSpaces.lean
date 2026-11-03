import Yau.LeafProofs.L16EnergyEmbedding
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Finite Galerkin spaces in the actual closed energy graph. The generating
sequence is dense for the graph norm. Its finite spans are mapped into spatial
`L²`, where their standard orthonormal bases are lifted by the injective value
map. Every dimension, including zero, is allowed. -/
open MeasureTheory Filter TopologicalSpace
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
variable {n : ℕ}

/-- Spatial `L²` is second countable for the actual restricted volume measure. -/
instance energyValueLp_secondCountable (O : Set (Space n)) :
    SecondCountableTopology (Lp ℝ 2 (volume.restrict O)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact MeasureTheory.Lp.SecondCountableTopology

/-- The finite Hilbert sum of the actual spatial `L²` spaces is second countable. -/
instance energyGraphAmbient_secondCountable (O : Set (Space n)) :
    SecondCountableTopology (EnergyGraphAmbient O) := inferInstance

/-- The actual graph space inherits second countability as a subspace. -/
instance energyGraphSpace_secondCountable (O : Set (Space n)) :
    SecondCountableTopology (EnergyGraphSpace O) := inferInstance

/-- In particular, the actual graph space is separable; no extra hypothesis on
an abstract energy space is needed. -/
theorem energyGraphSpace_separable (O : Set (Space n)) :
    SeparableSpace (EnergyGraphSpace O) := inferInstance

/-- A chosen sequence dense in the actual graph norm. -/
def energyGalerkinSequence (O : Set (Space n)) : ℕ → EnergyGraphSpace O :=
  denseSeq (EnergyGraphSpace O)

theorem energyGalerkinSequence_denseRange (O : Set (Space n)) :
    DenseRange (energyGalerkinSequence O) := denseRange_denseSeq _

/-- The span of the first `m` vectors, with no independence assumption. -/
def energyGalerkinSpace (O : Set (Space n)) (m : ℕ) :
    Submodule ℝ (EnergyGraphSpace O) :=
  Submodule.span ℝ (Set.range (fun k : Fin m => energyGalerkinSequence O k))

instance energyGalerkinSpace_finiteDimensional (O : Set (Space n)) (m : ℕ) :
    FiniteDimensional ℝ (energyGalerkinSpace O m) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

@[simp] theorem energyGalerkinSpace_zero (O : Set (Space n)) :
    energyGalerkinSpace O 0 = ⊥ := by
  simp [energyGalerkinSpace]

/-- Each fixed generating vector lies in every later finite span. -/
theorem energyGalerkinSequence_mem {O : Set (Space n)} {k m : ℕ} (hkm : k < m) :
    energyGalerkinSequence O k ∈ energyGalerkinSpace O m :=
  Submodule.subset_span ⟨⟨k, hkm⟩, rfl⟩

theorem energyGalerkinSpace_monotone (O : Set (Space n)) :
    Monotone (energyGalerkinSpace O) := by
  intro m l hml
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact energyGalerkinSequence_mem (lt_of_lt_of_le k.isLt hml)

/-- A test from a fixed finite span stays in all subsequent Galerkin spaces. -/
theorem energyGalerkinSpace_mem_of_le {O : Set (Space n)} {m l : ℕ}
    {v : EnergyGraphSpace O} (hv : v ∈ energyGalerkinSpace O m) (hml : m ≤ l) :
    v ∈ energyGalerkinSpace O l := energyGalerkinSpace_monotone O hml hv

theorem energyGalerkinSequence_eventually_mem (O : Set (Space n)) (k : ℕ) :
    ∀ᶠ m in atTop, energyGalerkinSequence O k ∈ energyGalerkinSpace O m := by
  filter_upwards [eventually_gt_atTop k] with m hm
  exact energyGalerkinSequence_mem hm

theorem energyGalerkinSpace_eventually_mem {O : Set (Space n)} {m : ℕ}
    {v : EnergyGraphSpace O} (hv : v ∈ energyGalerkinSpace O m) :
    ∀ᶠ l in atTop, v ∈ energyGalerkinSpace O l := by
  filter_upwards [eventually_ge_atTop m] with l hl
  exact energyGalerkinSpace_mem_of_le hv hl

/-- The union of the actual finite spans is graph-norm dense. -/
theorem energyGalerkinSpace_dense_union (O : Set (Space n)) :
    Dense (⋃ m, (energyGalerkinSpace O m : Set (EnergyGraphSpace O))) := by
  apply (energyGalerkinSequence_denseRange O).mono
  rintro _ ⟨k, rfl⟩
  exact Set.mem_iUnion.mpr ⟨k + 1, energyGalerkinSequence_mem (Nat.lt_succ_self k)⟩

/-- The actual spatial `L²` image of the `m`th finite graph space. -/
def energyGalerkinValueSpace (O : Set (Space n)) (m : ℕ) :
    Submodule ℝ (Lp ℝ 2 (volume.restrict O)) :=
  (energyGalerkinSpace O m).map (energyValueProjection O).toLinearMap

instance energyGalerkinValueSpace_finiteDimensional (O : Set (Space n)) (m : ℕ) :
    FiniteDimensional ℝ (energyGalerkinValueSpace O m) :=
  Module.Finite.map _ _

@[simp] theorem energyGalerkinValueSpace_zero (O : Set (Space n)) :
    energyGalerkinValueSpace O 0 = ⊥ := by
  simp [energyGalerkinValueSpace]

theorem energyGalerkinValueSpace_monotone (O : Set (Space n)) :
    Monotone (energyGalerkinValueSpace O) :=
  fun _ _ h => Submodule.map_mono (energyGalerkinSpace_monotone O h)

/-- The image spaces also exhaust a dense subspace of spatial `L²`. -/
theorem energyGalerkinValueSpace_dense_union {O : Set (Space n)} (hO : IsOpen O) :
    Dense (⋃ m, (energyGalerkinValueSpace O m : Set (Lp ℝ 2 (volume.restrict O)))) := by
  apply ((energyValueProjection_denseRange hO).comp
    (energyGalerkinSequence_denseRange O) (energyValueProjection O).continuous).mono
  rintro _ ⟨k, rfl⟩
  exact Set.mem_iUnion.mpr ⟨k + 1,
    ⟨energyGalerkinSequence O k, energyGalerkinSequence_mem (Nat.lt_succ_self k), rfl⟩⟩

/-- At stage zero the basis index type is `Fin 0`. -/
@[simp] theorem energyGalerkinValueSpace_finrank_zero (O : Set (Space n)) :
    Module.finrank ℝ (energyGalerkinValueSpace O 0) = 0 := by
  simp

/-- The value map restricted to the finite span is an actual linear equivalence
onto its actual image. Openness supplies the already proved injectivity. -/
def energyGalerkinValueEquiv {O : Set (Space n)} (hO : IsOpen O) (m : ℕ) :
    energyGalerkinSpace O m ≃ₗ[ℝ] energyGalerkinValueSpace O m :=
  Submodule.equivMapOfInjective (energyValueProjection O).toLinearMap
    (energyValueProjection_injective hO) _

/-- A genuine `L²` orthonormal basis, indexed by the actual finite dimension. -/
def energyGalerkinValueBasis (O : Set (Space n)) (m : ℕ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (energyGalerkinValueSpace O m))) ℝ
      (energyGalerkinValueSpace O m) :=
  stdOrthonormalBasis ℝ _

/-- The same basis lifted to the graph-norm finite span. -/
def energyGalerkinGraphBasis {O : Set (Space n)} (hO : IsOpen O) (m : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (energyGalerkinValueSpace O m))) ℝ
      (energyGalerkinSpace O m) :=
  (energyGalerkinValueBasis O m).toBasis.map (energyGalerkinValueEquiv hO m).symm

/-- The lifted family as vectors in the actual energy graph space. -/
def energyGalerkinFamily {O : Set (Space n)} (hO : IsOpen O) (m : ℕ) :
    Fin (Module.finrank ℝ (energyGalerkinValueSpace O m)) → EnergyGraphSpace O :=
  fun k => energyGalerkinGraphBasis hO m k

@[simp] theorem energyGalerkinFamily_mem {O : Set (Space n)} (hO : IsOpen O) (m : ℕ)
    (k : Fin (Module.finrank ℝ (energyGalerkinValueSpace O m))) :
    energyGalerkinFamily hO m k ∈ energyGalerkinSpace O m :=
  (energyGalerkinGraphBasis hO m k).2

@[simp] theorem energyValueProjection_energyGalerkinFamily {O : Set (Space n)}
    (hO : IsOpen O) (m : ℕ)
    (k : Fin (Module.finrank ℝ (energyGalerkinValueSpace O m))) :
    energyValueProjection O (energyGalerkinFamily hO m k) =
      (energyGalerkinValueBasis O m k : Lp ℝ 2 (volume.restrict O)) := by
  change energyValueProjection O
    ((energyGalerkinValueEquiv hO m).symm (energyGalerkinValueBasis O m k) :
      energyGalerkinSpace O m) = _
  exact Submodule.map_equivMapOfInjective_symm_apply _
    (energyValueProjection_injective hO) _ _

theorem energyGalerkinFamily_value_orthonormal {O : Set (Space n)}
    (hO : IsOpen O) (m : ℕ) :
    Orthonormal ℝ (fun k => energyValueProjection O (energyGalerkinFamily hO m k)) := by
  simp_rw [energyValueProjection_energyGalerkinFamily]
  exact (energyGalerkinValueBasis O m).orthonormal.comp_linearIsometry
    (energyGalerkinValueSpace O m).subtypeₗᵢ

/-- The lifted family spans precisely the chosen finite graph space. -/
theorem energyGalerkinFamily_span {O : Set (Space n)} (hO : IsOpen O) (m : ℕ) :
    Submodule.span ℝ (Set.range (energyGalerkinFamily hO m)) =
      energyGalerkinSpace O m := by
  change Submodule.span ℝ (Set.range (fun k =>
    (energyGalerkinSpace O m).subtype (energyGalerkinGraphBasis hO m k))) = _
  have hb := (energyGalerkinGraphBasis hO m).span_eq
  apply_fun Submodule.map (energyGalerkinSpace O m).subtype at hb
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_subtype] using hb

theorem energyGalerkinValueEquiv_finrank {O : Set (Space n)} (hO : IsOpen O) (m : ℕ) :
    Module.finrank ℝ (energyGalerkinSpace O m) =
      Module.finrank ℝ (energyGalerkinValueSpace O m) :=
  (energyGalerkinValueEquiv hO m).finrank_eq

end Yau.LeafProofs.L16Aux
