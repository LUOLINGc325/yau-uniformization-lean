import Yau.Proofs.D02PhysicalWeighted
import Yau.Proofs.V03MetricQuadratic

open scoped Manifold Topology ContDiff Matrix
open MeasureTheory Filter Set

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem punctured_curve_contMDiffAt {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    {z : ℂ} (hz : z ∈ puncturedUnitDisc) :
    ContMDiffAt 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f z := by
  let D := puncturedCoordinateDomain f (f z)
  have hD := puncturedCoordinateDomain_isOpen f hf (f z)
  have hzD : z ∈ D := ⟨hz, mem_extChartAt_source (f z)⟩
  have hc := complex_holomorphic_contDiffOn hD (puncturedCoordinate_differentiableOn f hf (f z))
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.mdifferentiableAt (Yau.Proofs.B01Aux.puncturedUnitDisc_isOpen.mem_nhds hz)).continuousAt, ?_⟩
  exact (hc.contDiffAt (hD.mem_nhds hzD)).contMDiffAt

/-- The physical energy is continuous on the actual punctured disc. It is
computed in one valid local chart around each point, so no frame is supplied. -/
theorem physicalEnergy_continuousOn (g : SmoothMetric M) {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc) :
    ContinuousOn (fun z ↦ hermitianNormSq (g.form (f z)) (physicalCurveDerivative f z))
      puncturedUnitDisc := by
  intro z hz
  let y := f z
  let D := puncturedCoordinateDomain f y
  have hD := puncturedCoordinateDomain_isOpen f hf y
  have hzD : z ∈ D := ⟨hz, mem_extChartAt_source (f z)⟩
  have hc := complex_holomorphic_contDiffOn hD (puncturedCoordinate_differentiableOn f hf y)
  have hd : ContDiffOn ℂ ∞ (fun w ↦ fderiv ℂ (chartPt y ∘ f) w 1) D :=
    (hc.fderiv_of_isOpen (m := ∞) hD (by simp)).clm_apply contDiffOn_const
  have hp : ContinuousOn (fun w ↦ ((chartPt y ∘ f) w, fderiv ℂ (chartPt y ∘ f) w 1)) D :=
    hc.continuousOn.prodMk hd.continuousOn
  have hmaps : MapsTo (fun w ↦ ((chartPt y ∘ f) w, fderiv ℂ (chartPt y ∘ f) w 1)) D
      (cotangentTarget y) := by
    intro w hw
    exact ⟨(extChartAt (ComplexModel n) y).map_source hw.2, mem_univ _⟩
  have hquad := (hermitianChartNormSq_contDiffOn g y).continuousOn.comp hp hmaps
  have heq : ∀ w ∈ D, hermitianChartNormSq g.form y (chartPt y (f w))
      (fderiv ℂ (chartPt y ∘ f) w 1) =
      hermitianNormSq (g.form (f w)) (physicalCurveDerivative f w) := by
    intro w hw
    rw [hermitianChartNormSq_at_point g.form y (f w) hw.2,
      puncturedCoordinate_fderiv_apply f hf y hw,
      chartVec_tangentCoords y (f w) hw.2]
    rfl
  exact ((hquad.congr (fun w hw ↦ (heq w hw).symm)).continuousAt
    (hD.mem_nhds hzD)).continuousWithinAt

end Yau.NodeProofs.D02RemovableAux
