import Yau.Proofs.F04SupportedL2Pairing
import Yau.LeafProofs.L19HeatRegularityJoint

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- An actual supported pivot source has a genuine product-L2 chart
 representative, obtained by its actual zero extension and the bounded
 chart restriction. No joint evaluation map on L2 classes is assumed. -/
theorem supportedL2_chart_joint_representative
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {T : ℝ}
    (f : ℝ → Lp ℝ 2 (μ.restrict Ω)) (hf : MemLp f 2 (volume.restrict (Ioo 0 T)))
    (c : M.Carrier) {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) :
    ∃ F : Point n → ℝ, StronglyMeasurable F ∧ MemLp F 2 (productVolume O (Ioo 0 T)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T), (fun z => F (z, t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ (f t)) := by
  have hOvol : volume O < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono subset_closure) hOC.measure_lt_top
  let : IsFiniteMeasure (volume.restrict O) := isFiniteMeasure_restrict.mpr hOvol.ne
  let R := (scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt).comp (l2ZeroExtension μ Ω hΩ)
  exact scalarL2Path_exists_joint (R.comp_memLp' hf)

end Yau.F04Proof
