import Yau.Proofs.C05GradientFlowDefinitions
import Yau.Geometry.ParabolicCalculus

/-! Actual covariant scalar jets, using the same computed connection and
the fixed real Hessian definition consumed by the gradient-flow helper. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def scalarJet (k : HermitianField M) (f : M.Carrier → ℝ) (c : M.Carrier) :
    (m : ℕ) → ComplexVector n → CovTensor n m
  | 0 => fun z _ => inChart c f z
  | m + 1 => covariantD k c (scalarJet k f c m)

def scalarJetNorm (k : HermitianField M) (f : M.Carrier → ℝ)
    (m : ℕ) (x : M.Carrier) : ℝ :=
  Real.sqrt (covTensorNormSq (realMetricFn k x (chartPt x x))
    (scalarJet k f x m (chartPt x x)))

theorem scalarJet_one (k : HermitianField M) (f : M.Carrier → ℝ) (c : M.Carrier)
    (z : ComplexVector n) (a : RIdx n) :
    scalarJet k f c 1 z ![a] = rDeriv (inChart c f) z a := by
  simp [scalarJet, covariantD]

theorem scalarJet_two (k : HermitianField M) (f : M.Carrier → ℝ) (c : M.Carrier)
    (z : ComplexVector n) (a b : RIdx n) :
    scalarJet k f c 2 z ![a, b] =
      Yau.Proofs.C05GradientFlowAux.realHessInChart k f c z a b := by
  simp [scalarJet, covariantD, Yau.Proofs.C05GradientFlowAux.realHessInChart,
    Fin.sum_univ_succ]

end Yau.Proofs.C05Aux
