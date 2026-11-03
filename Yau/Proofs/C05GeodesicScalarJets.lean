import Yau.Proofs.C05GradientFlowGeodesicHessian
import Yau.Proofs.C05HessianPropagationDerivative
import Yau.Proofs.C05HessianPropagationNorm

/-! Actual scalar derivatives on the same complete geodesic flow. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GeodesicScalarJetsAux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux Yau.Proofs.C05HessianPropagationAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def geodesicScalar (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) : ℝ :=
  f (realGeodesicFlow g p t).proj

theorem geodesicScalar_contDiff (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) :
    ContDiff ℝ ∞ (geodesicScalar g f p) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have hb := (Bundle.contMDiff_proj (IB := 𝓘(ℝ,ComplexVector n)) (n := ∞)
    (TangentSpace 𝓘(ℝ,ComplexVector n))).comp (realGeodesicFlow_contMDiff g p)
  exact ((smoothFn_contMDiff f hf).comp hb).contDiff

theorem geodesicScalar_hasDerivAt (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) :
    HasDerivAt (geodesicScalar g f p) (scalarVelocity f (realGeodesicFlow g p t)) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let γ := realGeodesicFlow g p
  let x := (γ t).proj
  have hfc := ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_target x))).differentiableAt (by simp)
  have H := hfc.hasFDerivAt.comp_hasDerivAt t (realGeodesicFlow_baseCoords_hasDerivAt g p t)
  have H' := H.congr_deriv (df_inChart_frame f hf x x (mem_chart_source _ _) (γ t).2)
  have hcont := ((FiberBundle.continuous_proj (ComplexVector n)
    (TangentSpace 𝓘(ℝ,ComplexVector n))).comp (realGeodesicFlow_contMDiff g p).continuous).continuousAt (x := t)
  apply H'.congr_of_eventuallyEq
  filter_upwards [hcont.preimage_mem_nhds
    ((chartAt (ComplexVector n) x).open_source.mem_nhds (mem_chart_source _ _))] with s hs
  exact congrArg f ((extChartAt (ComplexModel n) x).left_inv (by
    simpa only [extChartAt_source,Set.mem_preimage,Function.comp_apply] using hs)).symm

theorem geodesicScalar_deriv (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) :
    deriv (geodesicScalar g f p) t = scalarVelocity f (realGeodesicFlow g p t) :=
  (geodesicScalar_hasDerivAt g f hf p t).deriv

theorem geodesicScalar_iteratedDeriv_two (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) :
    iteratedDeriv 2 (geodesicScalar g f p) t =
      realHess g.form f (realGeodesicFlow g p t).proj
        (realTangentEquiv _ (realGeodesicFlow g p t).2)
        (realTangentEquiv _ (realGeodesicFlow g p t).2) := by
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv (geodesicScalar g f p) = fun s => scalarVelocity f (realGeodesicFlow g p s) :=
    funext (geodesicScalar_deriv g f hf p)
  rw [he]
  exact (scalarVelocity_realGeodesic_hasDerivAt g f hf p t).deriv

theorem geodesicHessian_hasDerivAt (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) :
    let x := (realGeodesicFlow g p t).proj
    HasDerivAt (fun s => realHess g.form f (realGeodesicFlow g p s).proj
      (realTangentEquiv _ (realGeodesicFlow g p s).2)
      (realTangentEquiv _ (realGeodesicFlow g p s).2))
      (tensorEvalCLM (scalarJet g.form f x 3 (chartPt x x))
        ![realTangentCoords x x (realGeodesicFlow g p t).2,
          realTangentCoords x x (realGeodesicFlow g p t).2,
          realTangentCoords x x (realGeodesicFlow g p t).2]) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let γ := realGeodesicFlow g p
  let x := (γ t).proj
  let η := extChartAt (realPhaseModel n) (γ t) ∘ γ
  have hγ := (realGeodesicFlow_integral g p).isMIntegralCurveAt t
  have hη := (realGeodesic_chart_eventually g γ hγ).self_of_nhds
  have hV := hη.2.snd
  change HasDerivAt (fun s => (η s).2)
    (chartGeodesicAcceleration g.form x (η t).1 (η t).2) t at hV
  rw [chartGeodesicAcceleration_eq] at hV
  have H := chart_hessian_parallel_hasDerivAt g.form (metricSmooth_of_smoothMetric g) f hf x
    (fun s => (η s).1) (fun s => (η s).2) t (η t).2 hη.1 hη.2.fst hV
  have hself : η t = realPhaseChart x (γ t) :=
    realPhaseChart_eq_extChartAt (γ t) (γ t) (mem_chart_source _ _)
  rw [hself] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := realPhaseModel n) (γ t))] with s hs
  have hb := (realPhaseChart_source (γ t) (γ s)).mp hs
  dsimp only [η,Function.comp_apply]
  rw [realPhaseChart_eq_extChartAt (γ t) (γ s) hb]
  exact realHess_in_fixed_chart g.form (metricSmooth_of_smoothMetric g) f hf x
    (γ s).proj hb (γ s).2 (γ s).2

theorem geodesicScalar_iteratedDeriv_three (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) :
    let x := (realGeodesicFlow g p t).proj
    iteratedDeriv 3 (geodesicScalar g f p) t =
      tensorEvalCLM (scalarJet g.form f x 3 (chartPt x x))
        ![realTangentCoords x x (realGeodesicFlow g p t).2,
          realTangentCoords x x (realGeodesicFlow g p t).2,
          realTangentCoords x x (realGeodesicFlow g p t).2] := by
  dsimp only
  conv_lhs => rw [show 3=2+1 from rfl,iteratedDeriv_succ]
  have he : iteratedDeriv 2 (geodesicScalar g f p) = fun s =>
      realHess g.form f (realGeodesicFlow g p s).proj
        (realTangentEquiv _ (realGeodesicFlow g p s).2)
        (realTangentEquiv _ (realGeodesicFlow g p s).2) :=
    funext (geodesicScalar_iteratedDeriv_two g f hf p)
  rw [he]
  exact (geodesicHessian_hasDerivAt g f hf p t).deriv

theorem geodesicScalar_third_abs_le (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) :
    |iteratedDeriv 3 (geodesicScalar g f p) t| ≤
      scalarJetNorm g.form f 3 (realGeodesicFlow g p t).proj *
        (Real.sqrt (realTangentEnergy g.form p)) ^ 3 := by
  let x := (realGeodesicFlow g p t).proj
  let V := realTangentEquiv x (realGeodesicFlow g p t).2
  have hC : 0 ≤ scalarJetNorm g.form f 3 x := Real.sqrt_nonneg _
  have H := scalarJet_three_evaluation_le g.form f x V V hC le_rfl
  simp only [V,tangent_coordinates_real_equiv] at H
  rw [geodesicScalar_iteratedDeriv_three g f hf p]
  apply H.trans_eq
  rw [realNorm,realNormSq_realGeodesic_velocity]
  change scalarJetNorm g.form f 3 x * Real.sqrt (realTangentEnergy g.form p) *
      realTangentEnergy g.form p =
    scalarJetNorm g.form f 3 x * Real.sqrt (realTangentEnergy g.form p) ^ 3
  calc
    _ = scalarJetNorm g.form f 3 x * Real.sqrt (realTangentEnergy g.form p) *
        Real.sqrt (realTangentEnergy g.form p) ^ 2 := by
      exact congrArg (fun a : ℝ => scalarJetNorm g.form f 3 x *
        Real.sqrt (realTangentEnergy g.form p) * a)
        (Real.sq_sqrt (realTangentEnergy_nonneg g.form p)).symm
    _ = _ := by ring

end Yau.Proofs.C05GeodesicScalarJetsAux
