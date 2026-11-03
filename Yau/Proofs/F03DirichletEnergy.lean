import Yau.Proofs.F03L2Restriction
import Yau.LeafProofs.L19ScalarEnergyCompletion

/-! The actual supported closed scalar energy space on an open domain. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine compact smooth core whose topological support lies in O. -/
def dirichletCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    Submodule ℝ (ScalarEnergyDomain g μ hμ) where
  carrier := {f | tsupport (f : M.Carrier → ℝ) ⊆ O}
  zero_mem' := by simp
  add_mem' := by
    intro f k hf hk
    exact (tsupport_add (f : M.Carrier → ℝ) k).trans (union_subset hf hk)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right (fun _ : M.Carrier => c) (f : M.Carrier → ℝ)).trans hf

/-- Closure is taken in the already constructed genuine scalar energy space. -/
def dirichletEnergySubmodule (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    Submodule ℝ (ScalarEnergySpace g μ hμ) :=
  ((dirichletCore g μ hμ O).map
    (UniformSpace.Completion.toComplL : ScalarEnergyDomain g μ hμ →L[ℝ]
      ScalarEnergySpace g μ hμ).toLinearMap).topologicalClosure

abbrev DirichletEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :=
  ↥(dirichletEnergySubmodule g μ hμ O)

def dirichletCoreToEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : dirichletCore g μ hμ O) : DirichletEnergy g μ hμ O :=
  ⟨(f.val : ScalarEnergySpace g μ hμ),
    Submodule.le_topologicalClosure _ ⟨f.val, f.property, rfl⟩⟩

theorem dirichletEnergy_completeSpace (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := by
  unfold DirichletEnergy dirichletEnergySubmodule
  infer_instance

/-- Inclusion is actual L² restriction of the ambient energy inclusion. -/
def dirichletL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    DirichletEnergy g μ hμ O →L[ℝ] Lp ℝ 2 (μ.restrict O) :=
  (l2Restriction μ O).comp ((scalarEnergyL2 g μ hμ).comp
    (dirichletEnergySubmodule g μ hμ O).subtypeL)

theorem dirichletL2_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (v : DirichletEnergy g μ hμ O) : ‖dirichletL2 g μ hμ O v‖ ≤ ‖v‖ := by
  exact (restrictL2_norm_le μ O _).trans (scalarEnergyL2_norm_le g μ hμ v.val)

theorem dirichletL2_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : dirichletCore g μ hμ O) :
    dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) =
      l2Restriction μ O (scalarEnergyDomainL2 g μ hμ f.val) := by
  change l2Restriction μ O (scalarEnergyL2 g μ hμ (f.val : ScalarEnergySpace g μ hμ)) = _
  rw [scalarEnergyL2_coe]

/-- Every element of the supported closure really has zero extension equal
to its original ambient L² image; no trace characterization is assumed. -/
theorem dirichletL2_zeroExtension (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (v : DirichletEnergy g μ hμ O) :
    l2ZeroExtension μ O hO (dirichletL2 g μ hμ O v) = scalarEnergyL2 g μ hμ v.val := by
  let S := (dirichletCore g μ hμ O).map
    (UniformSpace.Completion.toComplL : ScalarEnergyDomain g μ hμ →L[ℝ]
      ScalarEnergySpace g μ hμ).toLinearMap
  let P : Set (ScalarEnergySpace g μ hμ) :=
    {w | l2ZeroExtension μ O hO (l2Restriction μ O (scalarEnergyL2 g μ hμ w)) =
      scalarEnergyL2 g μ hμ w}
  have hclosed : IsClosed P := isClosed_eq
    ((l2ZeroExtension μ O hO).continuous.comp
      ((l2Restriction μ O).continuous.comp (scalarEnergyL2 g μ hμ).continuous))
    (scalarEnergyL2 g μ hμ).continuous
  have hcore : (S : Set (ScalarEnergySpace g μ hμ)) ⊆ P := by
    rintro _ ⟨f, hf, rfl⟩
    change l2ZeroExtension μ O hO (l2Restriction μ O
      (scalarEnergyL2 g μ hμ (f : ScalarEnergySpace g μ hμ))) =
        scalarEnergyL2 g μ hμ (f : ScalarEnergySpace g μ hμ)
    rw [scalarEnergyL2_coe]
    apply l2ZeroExtension_restriction_of_ae_zero
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ f] with x hx
    intro hxo
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun hs => hxo (hf hs))
  exact (closure_minimal hcore hclosed) v.property

theorem dirichletL2_injective (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) :
    Function.Injective (dirichletL2 g μ hμ O) := by
  intro v w hvw
  apply Subtype.ext
  apply scalarEnergyL2_injective g hK μ hμ
  rw [← dirichletL2_zeroExtension g μ hμ O hO v,
    ← dirichletL2_zeroExtension g μ hμ O hO w, hvw]

end Yau.Proofs.F03Aux
