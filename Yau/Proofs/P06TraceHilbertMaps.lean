import Yau.Proofs.P06FiberContraction
import Yau.Proofs.P06WeitzenbockCoreMaps
import Yau.LeafProofs.L03CutoffEnergyBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem omega_bound (g : SmoothMetric M) (x : M.Carrier) :
    formNormSq g.form (omegaForm g.form) x ≤ ((n : ℝ) + 1) ^ 2 := by
  rw [P06Weitzenbock.omegaForm_normSq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

def contraction (g : SmoothMetric M) (μ : Measure M.Carrier) :
    L2FormHilbert g μ 2 →L[ℝ] L2FormHilbert g μ 0 :=
  fiberContractionHilbert g μ (omegaForm g.form)
    (omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g))
    ((n : ℝ) + 1) (by positivity) (omega_bound g)

theorem contraction_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (fiberContraction g.form (omegaForm g.form) A) :=
  l2RealForm_fiberContraction g μ (omegaForm g.form)
    (omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g))
    ((n : ℝ) + 1) (omega_bound g) A hA

theorem contraction_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) :
    contraction g μ (realizeActualForm g μ A hA) =
      realizeActualForm g μ (fiberContraction g.form (omegaForm g.form) A)
        (contraction_l2 g μ A hA) :=
  fiberContractionHilbert_realize g μ (omegaForm g.form)
    (omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g))
    ((n : ℝ) + 1) (by positivity) (omega_bound g) (L2FormSpace.ofSection A hA)

theorem contraction_eq_trace (h : HermitianField M) (A : RealForm M 2)
    (hA : RealOneOne A) :
    fiberContraction h (omegaForm h) A = scalarForm (formTrace h A) := by
  change scalarForm (formInner h A (omegaForm h)) = _
  congr 1
  exact (funext (formTrace_eq_inner_omega h A hA)).symm

theorem trace_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) :
    L2RealForm g.form μ (scalarForm (formTrace g.form A)) := by
  rw [← contraction_eq_trace g.form A h11]
  exact contraction_l2 g μ A hA

theorem trace_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) :
    contraction g μ (realizeActualForm g μ A hA) =
      realizeActualForm g μ (scalarForm (formTrace g.form A)) (trace_l2 g μ A hA h11) := by
  simpa only [contraction_eq_trace g.form A h11] using contraction_realize g μ A hA

def omegaAdjoint (g : SmoothMetric M) (μ : Measure M.Carrier) :
    L2FormHilbert g μ 0 →L[ℝ] L2FormHilbert g μ 2 :=
  (contraction g μ).adjoint

theorem omegaAdjoint_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u : L2FormHilbert g μ 2) (v : L2FormHilbert g μ 0) :
    inner ℝ u (omegaAdjoint g μ v) = inner ℝ (contraction g μ u) v :=
  (contraction g μ).adjoint_inner_right u v

theorem contraction_projection (h : HermitianField M) (A : RealForm M 2) :
    fiberContraction h (omegaForm h) (P06Weitzenbock.oneOneProjection A) =
      fiberContraction h (omegaForm h) A := by
  change scalarForm _ = scalarForm _
  congr 1
  funext x
  rw [P06Weitzenbock.formInner_oneOneProjection_selfadjoint,
    P06Weitzenbock.oneOneProjection_fixed _ (omegaForm_oneOne h)]

theorem compact_trace_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    Integrable (formTrace g.form (multiplyRealForm η A)) μ := by
  have hω := omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)
  have hηω := smooth_compactlySupported_l2RealForm g μ hμ _
    (smoothRealForm_multiply η _ hη hω)
    (compactlySupportedRealForm_multiply_scalar η hcη (omegaForm g.form))
  have hη11 : RealOneOne (multiplyRealForm η A) := by
    intro x u v
    change η x * A x ![Complex.I • u, Complex.I • v] = η x * A x ![u, v]
    rw [h11 x u v]
  apply (formInner_integrable g μ A _ hA hηω).congr
  exact Filter.Eventually.of_forall fun x => by
    rw [formTrace_eq_inner_omega _ _ hη11,
      multiplyRealForm_inner_left, multiplyRealForm_inner_right]

end Yau.NodeProofs.P06Aux.TraceHilbert
