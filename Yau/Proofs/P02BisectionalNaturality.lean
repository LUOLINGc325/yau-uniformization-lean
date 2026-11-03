import Yau.Proofs.P02CurvaturePair
import Yau.LeafProofs.L23JetNaturality

noncomputable section
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem coordinateRm_eq_tensorEval (h : HermitianField M) (c : M.Carrier)
    (z U V W T : ComplexVector n) :
    coordinateRm h c z U V W T = tensorEvalCLM (rmTensor h c z) ![U,V,W,T] := by
  rw [tensorEvalCLM_apply]
  simp only [sum_tensor_cons, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, Fintype.sum_unique,
    Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change curvature4 h c z i j k l * _ * _ * _ * _ =
    curvature4 h c z i j k l * (_ * (_ * (_ * _)))
  ring

theorem coordinateRm_change (h : HermitianField M) (hs : MetricSmooth h)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source)
    (U V W T : ComplexVector n) :
    coordinateRm h c z U V W T =
      coordinateRm h d (realChartChange c d z)
        (fderiv ℝ (realChartChange c d) z U) (fderiv ℝ (realChartChange c d) z V)
        (fderiv ℝ (realChartChange c d) z W) (fderiv ℝ (realChartChange c d) z T) := by
  rw [coordinateRm_eq_tensorEval, coordinateRm_eq_tensorEval]
  have H := rmJet_eval_chart_change h hs 0 c d hz hy
  change tensorEvalCLM (rmTensor h c z) =
    (tensorEvalCLM (rmTensor h d (realChartChange c d z))).compContinuousLinearMap
      (fun _ : Fin 4 => fderiv ℝ (realChartChange c d) z) at H
  rw [H, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem coordinateRm_realTangent_change (h : HermitianField M) (hs : MetricSmooth h)
    (c d y : M.Carrier)
    (hc : y ∈ (chartAt (ComplexVector n) c).source)
    (hd : y ∈ (chartAt (ComplexVector n) d).source)
    (U V W T : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    coordinateRm h c (chartPt c y)
      (realTangentCoords c y U) (realTangentCoords c y V)
      (realTangentCoords c y W) (realTangentCoords c y T) =
    coordinateRm h d (chartPt d y)
      (realTangentCoords d y U) (realTangentCoords d y V)
      (realTangentCoords d y W) (realTangentCoords d y T) := by
  have hc' : y ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [extChartAt_source] using hc
  have hd' : y ∈ (extChartAt (ComplexModel n) d).source := by
    simpa only [extChartAt_source] using hd
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hc'
  have hinv : chartInv c (chartPt c y) = y := (extChartAt (ComplexModel n) c).left_inv hc'
  have hy : chartInv c (chartPt c y) ∈ (extChartAt (ComplexModel n) d).source := by
    rwa [hinv]
  have hD (Z : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
      fderiv ℝ (realChartChange c d) (chartPt c y) (realTangentCoords c y Z) =
        realTangentCoords d y Z := by
    rw [realChartChange_fderiv c d hz hy, hinv,
      ← realFrameCLM_apply c y hc, realFrameCLM_realTangentCoords c y hc]
  rw [coordinateRm_change h hs c d hz hy, hD, hD, hD, hD]
  have hchange : realChartChange c d (chartPt c y) = chartPt d y := by
    change chartPt d (chartInv c (chartPt c y)) = _
    rw [hinv]
  rw [hchange]

def transportBisectional (h : HermitianField M) (q : realTransportBundle M) : ℝ :=
  paperBisectionalNumerator h q.proj (realTangentEquiv q.proj q.2.1)
    (realTangentEquiv q.proj q.2.2)

theorem transportBisectional_in_chart (h : HermitianField M) (hs : MetricSmooth h)
    (c : M.Carrier) (q : realTransportBundle M)
    (hc : q.proj ∈ (chartAt (ComplexVector n) c).source) :
    transportBisectional h q = coordinateBisectional h c (chartPt c q.proj)
      (realTangentCoords c q.proj q.2.1) (realTangentCoords c q.proj q.2.2) := by
  rw [transportBisectional, paperBisectional_eq_coordinate]
  rw [← realTangentCoords_eq_complex_coords q.proj q.proj (mem_chart_source _ _),
    ← realTangentCoords_eq_complex_coords q.proj q.proj (mem_chart_source _ _)]
  unfold coordinateBisectional
  rw [← realTangentCoords_realTangentJ q.proj q.proj (mem_chart_source _ _),
    ← realTangentCoords_realTangentJ c q.proj hc]
  rw [coordinateRm_realTangent_change h hs q.proj c q.proj (mem_chart_source _ _) hc,
    coordinateRm_realTangent_change h hs q.proj c q.proj (mem_chart_source _ _) hc]

end Yau.NodeProofs.P02Aux
