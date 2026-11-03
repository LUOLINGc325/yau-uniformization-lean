import Yau.Proofs.F03DirichletEnergy
import Yau.LeafProofs.L19HeatRegularityWeakGradient
import Yau.LeafProofs.L19HeatRegularityJoint

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual L2 energy paths have actual joint chart values and actual joint
 chart differentials, constructed in product L2 from their genuine bounded
 chart maps. No continuous evaluation of L2 classes is postulated. -/
theorem dirichletEnergy_chart_joint_representatives
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) {T : ℝ} (U : ℝ → DirichletEnergy g μ hμ Ω)
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T))) (c : M.Carrier)
    {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) :
    ∃ (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ),
      StronglyMeasurable u ∧ (∀ i, StronglyMeasurable (fun p => G p i)) ∧
      MemLp u 2 (productVolume O (Ioo 0 T)) ∧
      (∀ i, MemLp (fun p => G p i) 2 (productVolume O (Ioo 0 T))) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T),
        ((fun z => u (z, t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (scalarEnergyL2 g μ hμ (U t).val)) ∧
        ∀ i, (fun z => G (z, t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt i (U t).val := by
  have hOvol : volume O < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono subset_closure) hOC.measure_lt_top
  let : IsFiniteMeasure (volume.restrict O) := isFiniteMeasure_restrict.mpr hOvol.ne
  let A := (dirichletEnergySubmodule g μ hμ Ω).subtypeL
  let R := (scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt).comp (scalarEnergyL2 g μ hμ)
  let D := fun i => scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt i
  have hUA := A.comp_memLp' hU
  obtain ⟨u, huM, huL, huSlice⟩ := scalarL2Path_exists_joint (R.comp_memLp' hUA)
  have hgrad (i : Yau.RIdx n) := scalarL2Path_exists_joint ((D i).comp_memLp' hUA)
  choose G hGM hGL hGS using hgrad
  refine ⟨u, (fun p i => G i p), huM, hGM, huL, hGL, ?_⟩
  have hGSall := ae_all_iff.mpr hGS
  filter_upwards [huSlice, hGSall] with t hut hGt
  refine ⟨?_, hGt⟩
  simpa only [Function.comp_apply, R, ContinuousLinearMap.comp_apply, A, Submodule.subtypeL_apply] using hut

end Yau.F04Proof
