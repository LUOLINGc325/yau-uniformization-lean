import Yau.Proofs.F01ChartCurvatureTransport
import Yau.Proofs.F01ChernCurvatureMatrix

/-! The diagonal curvature in the actual holomorphic normal frame is the
original native bisectional form on the two actual coordinate differentials. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem pullback_curvature_diagonal_bisectional (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (i a : Fin n) :
    let J := linearMatrix (coordinateDifferential e (e z) z)
    (BundleDbar.curvatureMatrix (pullbackMatrix g e) z i i a a).re =
      bisectionalForm g (e z) (WithLp.toLp 2 (fun k => J k a))
        (WithLp.toLp 2 (fun k => J k i)) := by
  dsimp only
  have hh := curvatureMatrix_holomorphic_chart g hg e he hei hz i i
  dsimp only at hh
  rw [hh]
  unfold bisectionalForm
  congr 1
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  conv_lhs =>
    arg 2
    ext l
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [curvatureMatrix_native_chern g hg]
  ring

end Yau.NodeProofs.F01Aux
