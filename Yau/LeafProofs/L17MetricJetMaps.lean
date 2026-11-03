import Yau.LeafProofs.L17CoefficientJets
import Yau.LeafProofs.L17RealificationAlgebra

/-! Linear reconstruction of the actual real metric and inverse metric jets. -/

noncomputable section

open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance metricJet_dualGroup : NormedAddCommGroup (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance metricJet_dualSpace : NormedSpace ℝ (ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance metricJet_bilinGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance
local instance metricJet_bilinSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) := inferInstance

def matrixEntryCLM {ι κ A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (a : ι) (b : κ) : Matrix ι κ A →L[ℝ] A where
  toFun H := H a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem matrixEntryCLM_apply {ι κ A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (a : ι) (b : κ) (H : Matrix ι κ A) : matrixEntryCLM a b H = H a b := rfl

def scalarRealificationCLM : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (RIdx n) (RIdx n) ℝ where
  toFun := scalarRealification
  map_add' A B := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b <;> simp [scalarRealification]
    ring
  map_smul' c A := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b <;> simp [scalarRealification]
  cont := by
    change Continuous (fun H : Matrix (Fin n) (Fin n) ℂ =>
      (fun a b => scalarRealification H a b : RIdx n → RIdx n → ℝ))
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    unfold scalarRealification
    split_ifs <;> fun_prop

theorem scalarRealificationCLM_apply (H : Matrix (Fin n) (Fin n) ℂ) :
    scalarRealificationCLM H = scalarRealification H := rfl

def matrixBilinearMap : Matrix (RIdx n) (RIdx n) ℝ →L[ℝ]
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  ∑ a, ∑ b,
    (matrixEntryCLM a b).smulRight
      ((L12Aux.realCoordCLM a).smulRight (L12Aux.realCoordCLM b))

theorem matrixBilinearMap_apply (H : Matrix (RIdx n) (RIdx n) ℝ)
    (u v : ComplexVector n) :
    matrixBilinearMap H u v =
      ∑ a, ∑ b, H a b * realCoord u a * realCoord v b := by
  simp only [matrixBilinearMap, sum_apply, ContinuousLinearMap.smulRight_apply,
    matrixEntryCLM_apply,
    L12Aux.realCoordCLM_apply, smul_apply, smul_eq_mul, mul_assoc]

theorem matrixBilinearMap_reconstruct
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    matrixBilinearMap (bilinearMatrix B) = B := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixBilinearMap_apply, L12Aux.realBilin_eq_sum B u v]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [bilinearMatrix]
  ring

def realMetricMap : Matrix (Fin n) (Fin n) ℂ →L[ℝ]
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  (2 : ℝ) • matrixBilinearMap.comp scalarRealificationCLM

theorem backgroundMetric_eq_realMetricMap
    (g : HermitianField M) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    backgroundMetric g e z = realMetricMap (pullbackMatrix g e z) := by
  calc
    _ = matrixBilinearMap (bilinearMatrix (backgroundMetric g e z)) :=
      (matrixBilinearMap_reconstruct _).symm
    _ = matrixBilinearMap ((2 : ℝ) • scalarRealification (pullbackMatrix g e z)) := by
      rw [backgroundMetric_bilinearMatrix g e he hz]
    _ = _ := by
      simp only [map_smul, realMetricMap, smul_apply, ContinuousLinearMap.comp_apply,
        scalarRealificationCLM_apply]

def matrixInverseBilinearMap : Matrix (RIdx n) (RIdx n) ℝ →L[ℝ]
    (ComplexVector n →L[ℝ] ℝ) →L[ℝ] ComplexVector n :=
  ∑ c, ∑ b,
    (matrixEntryCLM c b).smulRight
      ((ContinuousLinearMap.apply ℝ ℝ (realVec b)).smulRight (realVec c))

theorem inverseBilinear_eq_matrixInverseBilinearMap
    (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ) :
    inverseBilinear B = matrixInverseBilinearMap (bilinearMatrix B)⁻¹ := by
  simp only [inverseBilinear, matrixInverseBilinearMap, sum_apply,
    ContinuousLinearMap.smulRight_apply, matrixEntryCLM_apply]

def realInverseMetricMap : Matrix (Fin n) (Fin n) ℂ →L[ℝ]
    (ComplexVector n →L[ℝ] ℝ) →L[ℝ] ComplexVector n :=
  (1 / 2 : ℝ) • matrixInverseBilinearMap.comp scalarRealificationCLM

theorem inverse_backgroundMetric_eq_realInverseMetricMap
    (g : HermitianField M) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    inverseBilinear (backgroundMetric g e z) =
      realInverseMetricMap (pullbackMatrix g e z)⁻¹ := by
  rw [inverseBilinear_eq_matrixInverseBilinearMap,
    backgroundMetric_bilinearMatrix g e he hz,
    twice_scalarRealification_inverse _
      (isUnit_iff_ne_zero.mpr (pullbackMatrix_posDef g e he hei hz).det_pos.ne'),
    map_smul]
  simp only [realInverseMetricMap, smul_apply, ContinuousLinearMap.comp_apply,
    scalarRealificationCLM_apply]

theorem BoundedChartFamily.backgroundMetric_uniformJetBounds
    (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p => backgroundMetric g (A.chart p)) (fun _ => ball 0 A.radius) := by
  apply ((A.pullbackMatrix_uniformJetBounds k).comp_clm (fun _ => isOpen_ball)
    A.pullbackMatrix_smooth realMetricMap).congr (fun _ => isOpen_ball)
  intro p z hz
  exact (backgroundMetric_eq_realMetricMap g (A.chart p) (A.differentiable p)
    (A.closedBall_source p (ball_subset_closedBall hz))).symm

theorem BoundedChartFamily.inverse_backgroundMetric_smooth
    (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => inverseBilinear (backgroundMetric g (A.chart p) z))
      (ball 0 A.radius) := by
  apply (realInverseMetricMap.contDiff.comp_contDiffOn (A.inverseMatrix_smooth p)).congr
  intro z hz
  exact inverse_backgroundMetric_eq_realInverseMetricMap g (A.chart p)
    (A.differentiable p) (A.inverse_differentiable p)
    (A.closedBall_source p (ball_subset_closedBall hz))

theorem BoundedChartFamily.inverse_backgroundMetric_uniformJetBounds
    (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => inverseBilinear (backgroundMetric g (A.chart p) z))
      (fun _ => ball 0 A.radius) := by
  have hs (p : M.Carrier) : ContDiffOn ℝ ∞
      (fun z => (pullbackMatrix g (A.chart p) z)⁻¹) (ball 0 A.radius) :=
    L07Aux.matrix_inv_contDiffOn _ (A.pullbackMatrix_smooth p) fun z hz =>
      (pullbackMatrix_posDef g (A.chart p) (A.differentiable p) (A.inverse_differentiable p)
        (A.closedBall_source p (ball_subset_closedBall hz))).det_pos.ne'
  apply ((A.inverseMatrix_uniformJetBounds k).comp_clm (fun _ => isOpen_ball)
    hs realInverseMetricMap).congr (fun _ => isOpen_ball)
  intro p z hz
  exact (inverse_backgroundMetric_eq_realInverseMetricMap g (A.chart p)
    (A.differentiable p) (A.inverse_differentiable p)
    (A.closedBall_source p (ball_subset_closedBall hz))).symm

end Yau.LeafProofs.L17Aux
