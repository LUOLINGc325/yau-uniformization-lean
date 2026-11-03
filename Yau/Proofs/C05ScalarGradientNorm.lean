import Yau.Proofs.C05ScalarJetDefinitions
import Yau.Proofs.C05GradientFlowNorm
import Yau.LeafProofs.L23RicciBound

/-! The first actual scalar jet and the computed real gradient have the
same norm for the paper real metric `G = 2 Re h`. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarJet_one_normSq (k : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) :
    covTensorNormSq (realMetricFn k x (chartPt x x))
        (scalarJet k f x 1 (chartPt x x)) =
      ∑ a : RIdx n, ∑ b : RIdx n,
        (realMetricFn k x (chartPt x x))⁻¹ a b *
          rDeriv (inChart x f) (chartPt x x) a *
          rDeriv (inChart x f) (chartPt x x) b := by
  simp only [covTensorNormSq, sum_tensor_cons, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.prod_univ_zero, mul_one]
  simp only [scalarJet, covariantD, Finset.univ_eq_empty, Finset.sum_empty,
    sub_zero, Fintype.sum_unique, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem scalarJetNorm_one_eq_realGrad_norm (k : HermitianField M)
    (f : M.Carrier → ℝ) (x : M.Carrier) :
    scalarJetNorm k f 1 x =
      Yau.Proofs.C05GradientFlowAux.realNorm k x
        (Yau.Proofs.C05GradientFlowAux.realGrad k f x) := by
  rw [Yau.Proofs.C05GradientFlowAux.realNorm_realGrad_eq_inverse_metric]
  unfold scalarJetNorm
  rw [scalarJet_one_normSq]

end Yau.Proofs.C05Aux
