import Yau.Proofs.F01PenalizedHeatChain
import Yau.LeafProofs.L12

/-! The original metric-potential equation computes the actual native
Laplacian of its potential, retaining the dimension and Ricci terms. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem traceWith_self_posDef {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    traceWith H H = n := by
  unfold traceWith
  rw [Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom), Matrix.trace_one]
  simp

theorem potential_laplacian_identity (α k : HermitianField M) (u : M.Carrier → ℝ) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat α x - (t : ℂ) • ricci α x + levi u x) (x : M.Carrier) :
    laplacian k u x = n - traceWith (gMat k x) (gMat α x) +
      t * traceWith (gMat k x) (ricci α x) := by
  have hself : traceWith (gMat k x) (gMat k x) = n :=
    traceWith_self_posDef (Yau.LeafProofs.L12Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x))
  have htrace := congrArg (fun A => traceWith (gMat k x) A) (hpot x)
  rw [traceWith_add, traceWith_sub, traceWith_real_smul, hself] at htrace
  change traceWith (gMat k x) (levi u x) = _
  linarith

end Yau.NodeProofs.F01Aux
