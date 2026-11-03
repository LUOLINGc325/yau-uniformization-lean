import Yau.Proofs.C04BoundedGeometryChartsParallelFrameFlow
import Yau.Proofs.P02ParallelJ
import Yau.Proofs.P02Geodesic

/-! Parallel transport preserves the actual complex structure, with an
arbitrary complex-linear initial frame. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
  Yau.LeafProofs.L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem realTangentJ_eq_accepted (y : M.Carrier)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    realTangentJ y V = Yau.NodeProofs.P02Aux.realTangentJ y V := rfl

theorem parallel_frame_complex_of_initial (k : HermitianField M)
    (hs : MetricSmooth k) (hk : KahlerClosed k) (γ : ℝ → M.Carrier)
    (δ : ℝ) (hδ : 0 < δ) (hγ : FieldGeodesicOn k γ (Set.Ioo (-δ) (1 + δ)))
    (P : (s : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ s))
    (hP0 : ∀ w, P 0 (Complex.I • w) = realTangentJ (γ 0) (P 0 w))
    (hP : ∀ t ∈ Set.Ioo (-δ) (1 + δ), ∀ w : ComplexVector n,
      HasDerivAt (fun s => realTangentCoords (γ t) (γ s) (P s w))
        (-chartChristoffelBilin k (γ t) (chartPt (γ t) (γ t))
          (geoChartState γ (γ t) t).2 (realTangentCoords (γ t) (γ t) (P t w))) t) :
    ∀ t ∈ Set.Ioo (-δ) (1 + δ), ∀ w,
      P t (Complex.I • w) = realTangentJ (γ t) (P t w) := by
  letI := manifold_realSmooth M
  intro u hu w
  let W : (s : ℝ) → TangentSpace 𝓘(ℝ, ComplexVector n) (γ s) :=
    fun s => P s (Complex.I • w) - realTangentJ (γ s) (P s w)
  let F := fun s => (underlyingRealRiemannianMetric k).inner (γ s) (W s) (W s)
  have hF (t : ℝ) (ht : t ∈ Set.Ioo (-δ) (1 + δ)) : HasDerivAt F 0 t := by
    let c := γ t
    have hc : γ t ∈ (extChartAt (ComplexModel n) c).source := mem_extChartAt_source c
    have hc' : γ t ∈ (chartAt (ComplexVector n) c).source := by
      simpa only [extChartAt_source] using hc
    have hz : chartPt c (γ t) ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hc
    let Z := fun s => realTangentCoords c (γ s) (P s (Complex.I • w)) -
      Complex.I • realTangentCoords c (γ s) (P s w)
    have hV := (hP t ht w).const_smul Complex.I
    have hV' : HasDerivAt (fun s => Complex.I • realTangentCoords c (γ s) (P s w))
        (-chartChristoffelBilin k c (chartPt c (γ t)) (geoChartState γ c t).2
          (Complex.I • realTangentCoords c (γ t) (P t w))) t := by
      convert hV using 1
      rw [Yau.NodeProofs.P02Aux.chartChristoffelBilin_I_right k hs hk c hz, smul_neg]
    have hZ : HasDerivAt Z
        (-chartChristoffelBilin k c (chartPt c (γ t)) (geoChartState γ c t).2 (Z t)) t := by
      convert (hP t ht (Complex.I • w)).sub hV' using 1
      simp only [Z, map_sub]
      abel
    have hzt : HasDerivAt (fun s => chartPt c (γ s)) (geoChartState γ c t).2 t :=
      (hγ.2 c t ht hc).fst
    have H := realMetricInChart_parallelPair_hasDerivAt k hs c hz hzt hZ hZ
    apply H.congr_of_eventuallyEq
    have hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt (ComplexVector n) c).source :=
      (hγ.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht)).preimage_mem_nhds
        ((chartAt (ComplexVector n) c).open_source.mem_nhds hc')
    filter_upwards [hsrc] with s hsC
    have hZW : realTangentCoords c (γ s) (W s) = Z s := by
      simp only [W, Z, map_sub, realTangentJ_eq_accepted,
        Yau.NodeProofs.P02Aux.realTangentCoords_realTangentJ c (γ s) hsC]
    exact (realMetricInChart_tangentCoords k c (γ s) hsC (W s) (W s)).symm.trans (by rw [hZW])
  have hW0 : W 0 = 0 := by dsimp only [W]; rw [hP0, sub_self]
  have hF0 : F 0 = 0 := by simp only [F, hW0, map_zero, ContinuousLinearMap.zero_apply]
  have hZero : (0 : ℝ) ∈ Set.Ioo (-δ) (1 + δ) := by constructor <;> linarith
  have hFu : F u = 0 := by
    rw [← hF0]
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-δ) (1 + δ)).isPreconnected
      (fun t ht => (hF t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hF t ht).deriv) hu hZero
  have hWu : W u = 0 := by
    by_contra hn
    have H := (underlyingRealRiemannianMetric k).pos (γ u) (W u) hn
    change 0 < F u at H
    rw [hFu] at H
    exact lt_irrefl 0 H
  exact sub_eq_zero.mp hWu

end Yau.Proofs.C04ChartsAux
