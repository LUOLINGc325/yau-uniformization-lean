import Yau.Proofs.F01DiagonalHeat
import Yau.LeafProofs.L17ScalarChartOperator

/-! The actual local closed-time heat operator and metric trace agree
with the native manifold operators under the genuine holomorphic chart. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def fieldHeatWithin (h : ℝ → HermitianField M) (I : Set ℝ)
    (Q : ℝ → M.Carrier → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  derivWithin (fun s => Q s x) I t - laplacian (h t) (Q t) x

theorem traceWith_holomorphic_chart (g k : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    traceWith (pullbackMatrix g e z) (pullbackMatrix k e z) =
      traceWith (gMat g (e z)) (gMat k (e z)) := by
  rw [pullbackMatrix_eq_congruence g e (e z) z (mem_extChartAt_source (e z)),
    pullbackMatrix_eq_congruence k e (e z) z (mem_extChartAt_source (e z))]
  exact traceWith_congruence _ _ _ (linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e he hei (e z) hz (mem_extChartAt_source (e z))))

theorem diagonalHeatWithin_holomorphic_chart
    (h : ℝ → HermitianField M) (Q : ℝ → M.Carrier → ℝ) (I : Set ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (t : ℝ)
    (hQ : SmoothFn (Q t)) (values : Fin n → ℝ)
    (hdiag : pullbackMatrix (h t) e z = Matrix.diagonal (fun i => (values i : ℂ))) :
    diagonalHeatWithin values (fun p => Q p.2 (e p.1)) I z t =
      fieldHeatWithin h I Q (e z) t := by
  unfold diagonalHeatWithin fieldHeatWithin
  rw [← hdiag, traceWith_backgroundChart_eq_laplacian (h t) e he hei (Q t) hz
    (((hQ (e z)).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) (e z)).mem_nhds
        (mem_extChartAt_target (e z)))).of_le (by simp))]

end Yau.NodeProofs.F01Aux
