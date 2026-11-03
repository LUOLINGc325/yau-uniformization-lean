import Yau.Proofs.D02DifferentialNorm
import Yau.Proofs.D02DualCauchy

/-! The original sum of inverse-transpose squared covector norms is
exactly the trace of the same inverse metric times immersion Gram matrix. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

theorem inverse_gram_trace (H : Matrix (Fin n) (Fin n) ℂ) (J : Matrix (Fin N) (Fin n) ℂ) :
    (H⁻¹ * (Jᴴ * J)).trace =
      ∑ a, ∑ b, star (J a b) * ∑ c, H⁻¹ c b * J a c := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum]
  calc
    (∑ c, ∑ b, ∑ a, H⁻¹ c b * (star (J a b) * J a c)) =
        ∑ b, ∑ a, ∑ c, H⁻¹ c b * (star (J a b) * J a c) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem sum_row_dualNormMat_eq_trace (H : Matrix (Fin n) (Fin n) ℂ)
    (J : Matrix (Fin N) (Fin n) ℂ) :
    (∑ a, dualNormMat H (WithLp.toLp 2 (fun b => J a b))) = (H⁻¹ * (Jᴴ * J)).trace.re := by
  rw [inverse_gram_trace]
  simp only [dualNormMat, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    WithLp.ofLp_toLp, Pi.star_apply, Complex.re_sum]

theorem immersionDifferentialNormSq_eq_trace (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (y : M.Carrier) :
    immersionDifferentialNormSq g F y =
      ((gMat g y)⁻¹ * immersionGram F y (chartPt y y)).trace.re := by
  unfold immersionDifferentialNormSq
  have he : (∑ a, dualNorm g y (immersionComponentDifferential F a y)) =
      ∑ a, dualNormMat (gMat g y)
        (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F y (chartPt y y) a b)) := by
    apply Finset.sum_congr rfl
    intro a _
    unfold dualNorm
    rw [immersionComponentDifferential_coords hF y y (mem_extChartAt_source y)]
  rw [he, sum_row_dualNormMat_eq_trace]
  rfl

end Yau.NodeProofs.D02Aux
