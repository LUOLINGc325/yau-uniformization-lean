import Yau.Proofs.P02Connection
import Yau.LeafProofs.L23FieldMetricParallelVariation
import Yau.LeafProofs.L12JacobiCurvature

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

def realTangentJ (y : M.Carrier)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    TangentSpace 𝓘(ℝ, ComplexVector n) y :=
  (realTangentEquiv y).symm (Complex.I • realTangentEquiv y V)

theorem realTangentEquiv_realFrameCLM (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source) (v : ComplexVector n) :
    realTangentEquiv y (realFrameCLM c y v) = chartVec c y v := by
  have hy' : y ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [extChartAt_source] using hy
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hy'
  have hinv : chartInv c (chartPt c y) = y := (extChartAt (ComplexModel n) c).left_inv hy'
  have H := realTangentEquiv_realChartVec c (chartPt c y) v hz
  rw [← realCoordinateField_eq_realChartVec c (chartPt c y) v hz] at H
  rw [hinv] at H
  rw [realFrameCLM_apply c y hy]
  exact H

theorem realTangentCoords_eq_complex_coords (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    realTangentCoords c y V = tangentCoords c y (realTangentEquiv y V) := by
  have hy' : y ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [extChartAt_source] using hy
  have H := realTangentEquiv_realFrameCLM c y hy (realTangentCoords c y V)
  rw [realFrameCLM_realTangentCoords c y hy] at H
  have H' := congrArg (tangentCoords c y) H
  rw [tangentCoords_chartVec c y hy'] at H'
  exact H'.symm

theorem realTangentCoords_realTangentJ (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    realTangentCoords c y (realTangentJ y V) =
      Complex.I • realTangentCoords c y V := by
  rw [realTangentCoords_eq_complex_coords c y hy,
    realTangentCoords_eq_complex_coords c y hy, realTangentJ,
    ContinuousLinearEquiv.apply_symm_apply]
  exact (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) c) y).map_smul
    Complex.I (realTangentEquiv y V)

theorem realTangentJ_realFrameCLM (c y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) c).source) (v : ComplexVector n) :
    realTangentJ y (realFrameCLM c y v) = realFrameCLM c y (Complex.I • v) := by
  apply (realTangentEquiv y).injective
  rw [realTangentJ, ContinuousLinearEquiv.apply_symm_apply,
    realTangentEquiv_realFrameCLM c y hy,
    realTangentEquiv_realFrameCLM c y hy, chartVec_complex_smul]

theorem parallel_frame_I (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1 + δ)))
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (hP1 : (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1))
    (hP : ∀ (c : M.Carrier) (u : ℝ),
      u ∈ Set.Ioo (-δ) (1 + δ) →
      γ u ∈ (extChartAt (ComplexModel n) c).source →
      ∀ w : ComplexVector n,
        HasDerivAt (fun s => realTangentCoords c (γ s) (P s w))
          (-chartChristoffelBilin h c (chartPt c (γ u))
            (geoChartState γ c u).2
            (realTangentCoords c (γ u) (P u w))) u) :
    ∀ u ∈ Set.Ioo (-δ) (1 + δ), ∀ w : ComplexVector n,
      P u (Complex.I • w) = realTangentJ (γ u) (P u w) := by
  letI := manifold_realSmooth M
  intro u hu w
  let W : (s : ℝ) → TangentSpace 𝓘(ℝ, ComplexVector n) (γ s) :=
    fun s => P s (Complex.I • w) - realTangentJ (γ s) (P s w)
  let F : ℝ → ℝ := fun s =>
    (underlyingRealRiemannianMetric h).inner (γ s) (W s) (W s)
  have hF (t : ℝ) (ht : t ∈ Set.Ioo (-δ) (1 + δ)) : HasDerivAt F 0 t := by
    let c := γ t
    have hc : γ t ∈ (extChartAt (ComplexModel n) c).source := mem_extChartAt_source c
    have hc' : γ t ∈ (chartAt (ComplexVector n) c).source := by
      simpa only [extChartAt_source] using hc
    have hz : chartPt c (γ t) ∈ chartTarget c :=
      (extChartAt (ComplexModel n) c).map_source hc
    let Z : ℝ → ComplexVector n := fun s =>
      realTangentCoords c (γ s) (P s (Complex.I • w)) -
        Complex.I • realTangentCoords c (γ s) (P s w)
    have hV := (hP c t ht hc w).const_smul Complex.I
    have hV' : HasDerivAt (fun s => Complex.I • realTangentCoords c (γ s) (P s w))
        (-chartChristoffelBilin h c (chartPt c (γ t))
          (geoChartState γ c t).2
          (Complex.I • realTangentCoords c (γ t) (P t w))) t := by
      convert hV using 1
      rw [chartChristoffelBilin_I_right h hs hk c hz, smul_neg]
    have hZ : HasDerivAt Z
        (-chartChristoffelBilin h c (chartPt c (γ t))
          (geoChartState γ c t).2 (Z t)) t := by
      convert (hP c t ht hc (Complex.I • w)).sub hV' using 1
      simp only [Z, map_sub]
      abel
    have hzt : HasDerivAt (fun s => chartPt c (γ s)) (geoChartState γ c t).2 t :=
      (hγ.2 c t ht hc).fst
    have H := realMetricInChart_parallelPair_hasDerivAt h hs c hz hzt hZ hZ
    apply H.congr_of_eventuallyEq
    have hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt (ComplexVector n) c).source :=
      (hγ.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht)).preimage_mem_nhds
        ((chartAt (ComplexVector n) c).open_source.mem_nhds hc')
    filter_upwards [hsrc] with s hsC
    have hZW : realTangentCoords c (γ s) (W s) = Z s := by
      simp only [W, Z, map_sub, realTangentCoords_realTangentJ c (γ s) hsC]
    exact (realMetricInChart_tangentCoords h c (γ s) hsC (W s) (W s)).symm.trans
      (by rw [hZW])
  have hP1v (v : ComplexVector n) : P 1 v = realFrameCLM (γ 1) (γ 1) v :=
    congrArg (fun A : ComplexVector n →L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ 1) => A v) hP1
  have hW1 : W 1 = 0 := by
    dsimp [W]
    rw [hP1v, hP1v, realTangentJ_realFrameCLM (γ 1) (γ 1) (mem_chart_source _ _), sub_self]
  have hF1 : F 1 = 0 := by simp only [F, hW1, map_zero, ContinuousLinearMap.zero_apply]
  have hOne : (1 : ℝ) ∈ Set.Ioo (-δ) (1 + δ) := by constructor <;> linarith
  have hFu : F u = 0 := by
    rw [← hF1]
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-δ) (1 + δ)).isPreconnected
      (fun t ht => (hF t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hF t ht).deriv) hu hOne
  have hWu : W u = 0 := by
    by_contra hn
    have H := (underlyingRealRiemannianMetric h).pos (γ u) (W u) hn
    change 0 < F u at H
    rw [hFu] at H
    exact lt_irrefl 0 H
  change P u (Complex.I • w) - realTangentJ (γ u) (P u w) = 0 at hWu
  exact sub_eq_zero.mp hWu

end Yau.NodeProofs.P02Aux
