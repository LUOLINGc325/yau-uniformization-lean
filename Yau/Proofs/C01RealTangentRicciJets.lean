import Yau.Proofs.C01FieldRicciRealification
import Yau.Proofs.C01MetricQuadraticJets

/-! The actual real tangent speed evolves by its actual Ricci trace.
All tangent vectors lie in the fixed intrinsic fiber; no complete metric
structure is introduced for h_t. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

def realTangentSpeedSq (g : HermitianField M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : ℝ :=
  2 * hermitianNormSq (g x) (realTangentEquiv x v)

def actualRealRicciQuadratic (g : HermitianField M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : ℝ :=
  ∑ i, ∑ j, realRicciMatrix g x (chartPt x x) i j *
    realCoord (tangentCoords x x (realTangentEquiv x v)) i *
    realCoord (tangentCoords x x (realTangentEquiv x v)) j

theorem actualRealRicciQuadratic_eq_complex
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g)
    (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    actualRealRicciQuadratic g x v =
      2 * matrixQuadraticReal (ricci g x) (tangentCoords x x (realTangentEquiv x v)) :=
  realRicciMatrix_quadratic_eq_complex g hg hK x _

theorem realTangentSpeedSq_eq_matrix (g : HermitianField M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    realTangentSpeedSq g x v =
      2 * matrixQuadraticReal (gMat g x) (tangentCoords x x (realTangentEquiv x v)) := by
  have H := center_metric_quadratic_eq_normSq g x (tangentCoords x x (realTangentEquiv x v))
  rw [chartVec_tangentCoords x x (mem_extChartAt_source x)] at H
  exact congrArg (fun r : ℝ => 2 * r) H.symm

variable {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_realRicciQuadratic_bounds
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (a : ℝ) (ha : 0 ≤ a) (x : Pt X) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    0 ≤ actualRealRicciQuadratic (h a) x v ∧
      actualRealRicciQuadratic (h a) x v ≤ scalarCurvature (h a) x * realTangentSpeedSq (h a) x v := by
  have H := localizedFlow_realRicciMatrix_quadratic_bounds hflow hjoint a ha x
    (tangentCoords x x (realTangentEquiv x v))
  rw [realTangentSpeedSq_eq_matrix]
  exact ⟨H.1, H.2.trans_eq (by ring)⟩

theorem localizedFlow_realTangentSpeedSq_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun t => realTangentSpeedSq (h t) x v) (-actualRealRicciQuadratic (h a) x v) a := by
  let u := tangentCoords x x (realTangentEquiv x v)
  have heq : (fun t => realTangentSpeedSq (h t) x v) =
      (fun t => 2 * matrixQuadraticReal (gMat (h t) x) u) := by
    funext t
    exact realTangentSpeedSq_eq_matrix (h t) x v
  rw [heq, actualRealRicciQuadratic_eq_complex (h a)
    (localizedFlow_metricSmooth_nonneg hflow a ha.le) (hflow.1.2.2.1 a ha.le) x v]
  convert (localizedFlow_metric_quadratic_hasDerivAt hflow x ha (WithLp.ofLp u)).const_mul 2 using 1 <;>
    simp only [matrixQuadraticReal, mul_neg, u]

end Yau.NodeProofs.C01Aux
