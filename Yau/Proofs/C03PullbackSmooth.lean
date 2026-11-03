import Yau.Proofs.C03PullbackField
import Yau.Proofs.C03CutoffProducts
import Yau.Proofs.C04BoundedGeometryChartsMetric

/-! Smoothness of the genuine differential pullback is proved in one target
chart near each source point, without choosing a globally smooth frame. -/

noncomputable section
open Set Filter
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem sum_stdVec_coordinates (v : ComplexVector n) :
    (∑ i, v i • stdVec i) = v := by
  ext j
  simp [stdVec, EuclideanSpace.single, Pi.single_apply]

theorem hermitian_chart_pair (k : HermitianField M) (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) (u v : ComplexVector n) :
    (k y).toFun (chartVec a y u) (chartVec a y v) =
      ∑ i, ∑ j, star (u i) * hMat k a (chartPt a y) i j * v j := by
  have hsum (w : ComplexVector n) : chartVec a y w = ∑ i, w i • chartVec a y (stdVec i) := by
    unfold chartVec
    conv_lhs => rw [← sum_stdVec_coordinates w]
    simp only [map_sum, map_smul]
  rw [hsum u, hsum v, hermitian_sum_left]
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, Finset.mul_sum]
  have hInv : chartInv a (chartPt a y) = y := (extChartAt (ComplexModel n) a).left_inv hy
  have hHij (i j : Fin n) : hMat k a (chartPt a y) i j =
      (k y).toFun (chartVec a y (stdVec i)) (chartVec a y (stdVec j)) := by
    change (k (chartInv a (chartPt a y))).toFun
      (chartVec a (chartInv a (chartPt a y)) (stdVec i))
      (chartVec a (chartInv a (chartPt a y)) (stdVec j)) = _
    rw [hInv]
  simp only [hHij, mul_assoc]

theorem pullbackMat_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun w => pullbackMat k Φ w a b) (Metric.ball 0 r) := by
  intro w₀ hw₀
  let c := Φ w₀
  let U := Metric.ball (0 : ComplexVector n) r ∩ Φ ⁻¹' (chartAt (ComplexVector n) c).source
  have hU : IsOpen U := hΦ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball
    (chartAt (ComplexVector n) c).open_source
  have hwU : w₀ ∈ U := ⟨hw₀, mem_chart_source (ComplexVector n) c⟩
  let G : ComplexVector n → ComplexVector n := fun w => chartPt c (Φ w)
  have hG : ContDiffOn ℂ ∞ G U :=
    ((contMDiffOn_extChartAt (I := ComplexModel n) (x := c) (n := ∞)).comp
      (hΦ.mono inter_subset_left) (fun _ hw => hw.2)).contDiffOn
  have hd (v : ComplexVector n) : ContDiffOn ℝ ∞ (fun w => fderiv ℂ G w v) U :=
    ((hG.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const).restrict_scalars ℝ
  have heval (v : ComplexVector n) (i : Fin n) :
      ContDiffOn ℝ ∞ (fun w => (fderiv ℂ G w v) i) U :=
    ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn
      (hd v)
  have hmaps : MapsTo G U (chartTarget c) := by
    intro w hw
    exact (extChartAt (ComplexModel n) c).map_source
      (by simpa only [extChartAt_source, mem_preimage] using hw.2)
  have hm (i j : Fin n) : ContDiffOn ℝ ∞ (fun w => hMat k c (G w) i j) U :=
    (C04ChartsAux.field_coordinate_smooth k hk c i j).comp (hG.restrict_scalars ℝ) hmaps
  have hp : ContDiffOn ℝ ∞ (fun w => ∑ i, ∑ j,
      star ((fderiv ℂ G w (stdVec a)) i) * hMat k c (G w) i j *
        (fderiv ℂ G w (stdVec b)) j) U := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (((Complex.conjCLE.contDiff.comp_contDiffOn (heval (stdVec a) i)).mul
      (hm i j)).mul (heval (stdVec b) j))
  have heq : ∀ w ∈ U, (∑ i, ∑ j,
      star ((fderiv ℂ G w (stdVec a)) i) * hMat k c (G w) i j *
        (fderiv ℂ G w (stdVec b)) j) = pullbackMat k Φ w a b := by
    intro w hw
    have hs : Φ w ∈ (extChartAt (ComplexModel n) c).source :=
      by simpa only [extChartAt_source, mem_preimage] using hw.2
    have hΦd := (hΦ.contMDiffAt (Metric.isOpen_ball.mem_nhds hw.1)).mdifferentiableAt
      (by simp)
    have hdG (v : ComplexVector n) : fderiv ℂ G w v = tangentCoords c (Φ w)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ w v) := by
      have h := congrArg (fun L => L v)
        (mfderiv_comp (I := ComplexModel n) (I' := ComplexModel n)
          (I'' := ComplexModel n) w (mdifferentiableAt_extChartAt hw.2) hΦd)
      rw [mfderiv_eq_fderiv] at h
      exact h
    rw [← hermitian_chart_pair k c (Φ w) hs,
      hdG, hdG, chartVec_tangentCoords c (Φ w) (by simpa only [extChartAt_source] using hs),
      chartVec_tangentCoords c (Φ w) (by simpa only [extChartAt_source] using hs)]
    rfl
  exact ((hp.congr (fun w hw => (heq w hw).symm)).contDiffAt
    (hU.mem_nhds hwU)).contDiffWithinAt

end Yau.Proofs.C03Aux
