import Yau.Proofs.Y03ChartDerivative
import Yau.Proofs.Y03Frames
import Yau.Proofs.Y03MetricSmooth
import Yau.Proofs.Y03JointPullback

/-! Matrices of the actual center chart differentials in one fixed manifold chart. -/

open scoped Manifold Topology Matrix ContDiff
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {M : ComplexManifold n}

def centerFrameMatrix (o : M.Carrier) (Φ : ComplexVector n → M.Carrier) : Herm n :=
  Matrix.toEuclideanLin.symm
    (((mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) (extChartAt (ComplexModel n) o) o).comp
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ 0)).toLinearMap)

theorem centerFrameMatrix_toEuclideanCLM (o : M.Carrier) (Φ : ComplexVector n → M.Carrier) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (centerFrameMatrix o Φ) =
      (mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) (extChartAt (ComplexModel n) o) o).comp
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ 0) := by
  apply ContinuousLinearMap.coe_injective
  exact Matrix.toEuclideanLin.apply_symm_apply _

theorem centerFrameMatrix_chain (o : M.Carrier) {Φ Ψ : ComplexVector n → M.Carrier}
    {F : ComplexVector n → ComplexVector n} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hΨ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Ψ (Metric.ball 0 R))
    (hF : DifferentiableOn ℂ F (Metric.ball 0 r)) (hFzero : F 0 = 0)
    (hgerm : ∀ᶠ z in 𝓝 0, Ψ (F z) = Φ z) :
    centerFrameMatrix o Ψ * derivativeMatrix F = centerFrameMatrix o Φ := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective
  rw [map_mul]
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (centerFrameMatrix o Ψ)).comp
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (derivativeMatrix F)) = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (centerFrameMatrix o Φ)
  rw [centerFrameMatrix_toEuclideanCLM, centerFrameMatrix_toEuclideanCLM,
    derivativeMatrix_toEuclideanCLM]
  change ((mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) (extChartAt (ComplexModel n) o) o).comp
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Ψ 0)).comp (centerDeriv F) = _
  have hc := transition_center_mfderiv hr hR hΨ hF hFzero hgerm
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L =>
    (mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) (extChartAt (ComplexModel n) o) o) (L v)) hc

theorem chartVec_tangentCoords_self (o : M.Carrier) (v : TangentVector M o) :
    chartVec o o (tangentCoords o o v) = v := by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := ComplexModel n) (mem_extChartAt_source o)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  exact congrArg (fun L => L v) hcomp

theorem centerFrameMatrix_chartVec (o : M.Carrier) (Φ : ComplexVector n → M.Carrier)
    (i : Fin n) :
    chartVec o o (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (centerFrameMatrix o Φ) (stdVec i)) =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ 0 (stdVec i) := by
  rw [centerFrameMatrix_toEuclideanCLM]
  exact chartVec_tangentCoords_self o _

theorem chartVec_matrix_column (o : M.Carrier) (B : Herm n) (i : Fin n) :
    chartVec o o (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (stdVec i)) =
      ∑ a, B a i • chartVec o o (stdVec a) := by
  have hcolumn : ∀ a, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (stdVec i) a = B a i := by
    intro a
    simp [stdVec, EuclideanSpace.single, Matrix.mulVec_single]
  rw [← sum_stdVec (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (stdVec i))]
  exact (map_sum (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) o).symm (chartPt o o)) _ _).trans
      (Finset.sum_congr rfl fun a _ => by rw [hcolumn]; exact chartVec_smul o o _ _)

theorem gMat_conjugate_apply (h : HermitianField M) (o : M.Carrier) (B : Herm n) (i j : Fin n) :
    (B.conjTranspose * gMat h o * B) i j =
      (h o).toFun
        (chartVec o o (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (stdVec i)))
        (chartVec o o (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (stdVec j))) := by
  rw [chartVec_matrix_column, chartVec_matrix_column, hermitian_sum_left]
  have hpoint : chartInv o (chartPt o o) = o := (extChartAt (ComplexModel n) o).left_inv (mem_extChartAt_source o)
  have hg (a b : Fin n) : gMat h o a b =
      (h o).toFun (chartVec o o (stdVec a)) (chartVec o o (stdVec b)) := by
    unfold gMat hMat
    rw [hpoint]
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, Matrix.mul_apply, Matrix.conjTranspose_apply,
    hg, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem unitaryChart_centerFrame_gram {h : HermitianField M} {o : M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C : ℝ} (hchart : UnitaryChart h o Φ r c C) :
    (centerFrameMatrix o Φ).conjTranspose * gMat h o * centerFrameMatrix o Φ = 1 := by
  ext i j
  rw [gMat_conjugate_apply, centerFrameMatrix_chartVec, centerFrameMatrix_chartVec]
  have hgram := congrArg (fun A : Herm n => A i j) hchart.2.2.1
  unfold pullbackMat at hgram
  rw [hchart.2.1] at hgram
  exact hgram

end Yau.Blueprint.Alignment.Y03Proof
