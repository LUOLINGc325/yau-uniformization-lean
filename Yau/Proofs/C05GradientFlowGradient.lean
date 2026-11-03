import Yau.Proofs.C05GradientFlowCoordinates
import Yau.LeafProofs.L12ParallelTransport

/-! The computed gradient is the actual smooth real tangent vector field dual to df. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

def realGradientVectorField (k : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) : TangentSpace 𝓘(ℝ, ComplexVector n) x :=
  (realTangentEquiv x).symm (realGrad k f x)

def localGradientVectorField (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (x : M.Carrier) : TangentSpace 𝓘(ℝ, ComplexVector n) x :=
  realCoordinateVectorField c (realGradInChart k f c) x

theorem localGradientVectorField_coordinates (k : HermitianField M) (f : M.Carrier → ℝ)
    (c x : M.Carrier) (hx : x ∈ (chartAt (ComplexVector n) c).source) :
    realTangentCoords c x (localGradientVectorField k f c x) =
      realGradInChart k f c (chartPt c x) := by
  exact realTangentCoords_realCoordinateField c x hx _

theorem df_inChart_frame (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (c x : M.Carrier) (hx : x ∈ (chartAt (ComplexVector n) c).source)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    fderiv ℝ (inChart c f) (chartPt c x) (realTangentCoords c x v) =
      mvfderiv 𝓘(ℝ, ComplexVector n) f x v := by
  letI := manifold_realSmooth M
  have hs : x ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [extChartAt_source, Set.mem_preimage] using hx
  have hz := (extChartAt (ComplexModel n) c).map_source hs
  have hinv : chartInv c (chartPt c x) = x := (extChartAt (ComplexModel n) c).left_inv hs
  have hdf : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) f
      (chartInv c (chartPt c x)) := by
    rw [hinv]
    exact (smoothFn_contMDiff f hf).mdifferentiableAt (by simp)
  have H := mvfderiv_realCoordinateField_target f c (chartPt c x) (realTangentCoords c x v) hz hdf
  rw [hinv, ← realFrameCLM_apply c x hx, realFrameCLM_realTangentCoords c x hx] at H
  exact H.symm

theorem localGradientVectorField_dual (k : HermitianField M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (c x : M.Carrier) (hx : x ∈ (chartAt (ComplexVector n) c).source)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    (underlyingRealRiemannianMetric k).inner x (localGradientVectorField k f c x) v =
      mvfderiv 𝓘(ℝ, ComplexVector n) f x v := by
  have hz : chartPt c x ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source
    (by simpa only [extChartAt_source, Set.mem_preimage] using hx)
  rw [← realMetricInChart_tangentCoords k c x hx,
    localGradientVectorField_coordinates k f c x hx, realGradInChart_dual k f c _ hz,
    df_inChart_frame f hf c x hx]

theorem realGradientVectorField_eq_centre (k : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) : realGradientVectorField k f x = localGradientVectorField k f x x := by
  apply (realTangentEquiv x).injective
  change realTangentEquiv x ((realTangentEquiv x).symm (realGrad k f x)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  let z := chartPt x x
  let u := realGradInChart k f x z
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hi : chartInv x z = x := (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have H : realTangentEquiv (chartInv x z) (realCoordinateField x u (chartInv x z)) =
      chartVec x (chartInv x z) u := by
    rw [realCoordinateField_eq_realChartVec x z u hz]
    exact realTangentEquiv_realChartVec x z u hz
  rw [hi] at H
  exact H.symm

theorem realGradientVectorField_dual (k : HermitianField M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    (underlyingRealRiemannianMetric k).inner x (realGradientVectorField k f x) v =
      mvfderiv 𝓘(ℝ, ComplexVector n) f x v := by
  rw [realGradientVectorField_eq_centre]
  exact localGradientVectorField_dual k f hf x x (mem_chart_source _ _) v

theorem realMetric_dual_unique (k : HermitianField M) (x : M.Carrier)
    (u v : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (h : ∀ w, (underlyingRealRiemannianMetric k).inner x u w =
      (underlyingRealRiemannianMetric k).inner x v w) : u = v := by
  apply sub_eq_zero.mp
  by_contra hne
  have hp := (underlyingRealRiemannianMetric k).pos x (u - v) hne
  simp only [map_sub, ContinuousLinearMap.sub_apply] at hp
  linarith only [hp, h u, h v]

theorem realGradientVectorField_eq_local (k : HermitianField M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (c x : M.Carrier) (hx : x ∈ (chartAt (ComplexVector n) c).source) :
    realGradientVectorField k f x = localGradientVectorField k f c x := by
  apply realMetric_dual_unique k x
  intro w
  rw [realGradientVectorField_dual k f hf, localGradientVectorField_dual k f hf c x hx]

theorem realGradientVectorField_contMDiff (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ComplexVector n) (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) ∞
      (fun x => (⟨x, realGradientVectorField g.form f x⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) := by
  letI := manifold_realSmooth M
  intro x
  have hV := (realGradInChart_contDiffOn g f hf x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))
  have H := realCoordinateVectorField_contMDiffAt x x (mem_chart_source _ _)
    (realGradInChart g.form f x) hV
  apply H.congr_of_eventuallyEq
  filter_upwards [(chartAt (ComplexVector n) x).open_source.mem_nhds (mem_chart_source _ _)] with y hy
  exact congrArg (fun w => (⟨y, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier))
    (realGradientVectorField_eq_local g.form f hf x y hy)

end Yau.Proofs.C05GradientFlowAux
