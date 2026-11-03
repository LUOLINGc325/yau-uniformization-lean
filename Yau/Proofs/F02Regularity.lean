import Yau.Proofs.F02Elementary
import Yau.Blueprint.Nodes

/-! A direct use of the exact registered G04 normalization contract. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.F02Aux
open Yau Blueprint
open LeafProofs.L18Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

/-- Evaluating iota on the two actual coordinate pairs recovers both
parts of its represented matrix. -/
theorem formHermitianMatrix_of_representsIota
    (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ) (α : RealForm M 2)
    (hα : RepresentsIota A α) (x : M.Carrier) : formHermitianMatrix α x = A x := by
  ext a b
  have h₁ : (α x) ![chartVec x x (stdVec a), chartVec x x (stdVec b)] =
      2 * (A x a b).im := by
    simpa [stdVec, EuclideanSpace.single] using hα x (stdVec a) (stdVec b)
  have hI : (α x) ![chartVec x x (stdVec a), Complex.I • chartVec x x (stdVec b)] =
      2 * (A x a b).re := by
    have h := hα x (stdVec a) (Complex.I • stdVec b)
    rw [chartVec_smul] at h
    simpa [stdVec, EuclideanSpace.single] using h
  unfold formHermitianMatrix
  rw [h₁, hI]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- G04's exact Hodge/normalization components give regularity of the
actual initial scalar curvature, rather than an independent scalar datum. -/
theorem scalarCurvature_smooth_of_G04 (hG04 : G04) (X : KahlerManifold n) :
    SmoothFn (scalarCurvature X.metric.form) := by
  have hnorm := hG04.2.1 n X.manifold X.metric.form
    (metricSmooth_of_smoothMetric X.metric) X.kahler_metric
  obtain ⟨α, hαsmooth, hαone, _, hαiota, _⟩ := hnorm.2.2.2.2.2.1.2.2
  have htrace : SmoothFn (formTrace X.metric.form α) :=
    hnorm.2.2.2.1.1 α hαsmooth hαone
  have heq : formTrace X.metric.form α = scalarCurvature X.metric.form := by
    funext x
    rw [formTrace, formHermitianMatrix_of_representsIota _ _ hαiota]
    rfl
  rwa [heq] at htrace

end Yau.Proofs.F02Aux
