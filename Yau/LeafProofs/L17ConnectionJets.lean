import Yau.LeafProofs.L17MetricJetMaps

/-! All-order uniform jets of the computed real coordinate connection. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance connectionJets_dualGroup : NormedAddCommGroup (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance connectionJets_dualSpace : NormedSpace ℝ (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance connectionJets_bilinGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance connectionJets_bilinSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance connectionJets_trilinGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :=
  inferInstance
local instance connectionJets_trilinSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :=
  inferInstance
local instance connectionJets_firstGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance connectionJets_firstSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance connectionJets_secondGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance connectionJets_secondSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

def koszulOperator :
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) →L[ℝ]
      ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ := by
  let P := (ContinuousLinearMap.flipₗᵢ ℝ (ComplexVector n) (ComplexVector n)
    (ComplexVector n →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  let Q := (ContinuousLinearMap.flipₗᵢ ℝ (ComplexVector n) (ComplexVector n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let R := ContinuousLinearMap.compL ℝ (ComplexVector n)
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) Q
  exact (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ + P - R.comp P)

theorem koszulOperator_apply
    (D : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    koszulOperator D = koszulMap D := rfl

theorem BoundedChartFamily.backgroundConnection_smooth
    (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (backgroundConnection g (A.chart p)) (ball 0 A.radius) := by
  let L := ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n →L[ℝ] ℝ)
    (ComplexVector n)
  let B := ContinuousLinearMap.compL ℝ (ComplexVector n)
    (ComplexVector n →L[ℝ] (ComplexVector n →L[ℝ] ℝ))
    (ComplexVector n →L[ℝ] ComplexVector n)
  have hQ := L.contDiff.comp_contDiffOn (A.inverse_backgroundMetric_smooth p)
  have hD := (A.backgroundMetric_smooth p).fderiv_of_isOpen isOpen_ball
    (by simp : ∞ + 1 ≤ ∞)
  have hK := koszulOperator.contDiff.comp_contDiffOn hD
  apply (((contDiffOn_const (c := B)).clm_apply hQ).clm_apply hK).congr
  intro z hz
  rfl

theorem BoundedChartFamily.backgroundConnection_uniformJetBounds
    (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p => backgroundConnection g (A.chart p))
      (fun _ => ball 0 A.radius) := by
  let L := ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n →L[ℝ] ℝ)
    (ComplexVector n)
  let B := ContinuousLinearMap.compL ℝ (ComplexVector n)
    (ComplexVector n →L[ℝ] (ComplexVector n →L[ℝ] ℝ))
    (ComplexVector n →L[ℝ] ComplexVector n)
  have hD (p : M.Carrier) :=
    (A.backgroundMetric_smooth p).fderiv_of_isOpen isOpen_ball (by simp : ∞ + 1 ≤ ∞)
  have hQ (p : M.Carrier) := L.contDiff.comp_contDiffOn (A.inverse_backgroundMetric_smooth p)
  have hK (p : M.Carrier) := koszulOperator.contDiff.comp_contDiffOn (hD p)
  have hbQ := (A.inverse_backgroundMetric_uniformJetBounds k).comp_clm
    (fun _ => isOpen_ball) A.inverse_backgroundMetric_smooth L
  have hbD := (A.backgroundMetric_uniformJetBounds (k + 1)).fderiv
  have hbK := hbD.comp_clm (fun _ => isOpen_ball) hD koszulOperator
  apply (hbQ.bilinear hbK (fun _ => isOpen_ball) hQ hK B).congr (fun _ => isOpen_ball)
  intro p z hz
  rfl

end Yau.LeafProofs.L17Aux
