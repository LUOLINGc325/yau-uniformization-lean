import Yau.Proofs.F01ConformalGradientTrace

/-! The actual positive trace at the selected normal direction, including
all dimensions without introducing an artificial positive-dimension premise. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem conformal_normal_trace_pos (g k : HermitianField M)
    (f : M.Carrier → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ))) (a : Fin n) :
    0 < traceWith (pullbackMatrix k e 0) (pullbackMatrix (conformalField g f) e 0) := by
  have hv (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos k e he hei hs0 i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  have hs : 0 < ∑ i, (values i)⁻¹ :=
    (inv_pos.mpr (hv a)).trans_le
      (Finset.single_le_sum (fun i _ => inv_nonneg.mpr (hv i).le) (Finset.mem_univ a))
  rw [conformalField_pullbackMatrix, hvalue, hdiag,
    traceWith_real_diagonal_smul_one values (fun i => (hv i).ne')]
  exact mul_pos (Real.exp_pos _) hs

end Yau.NodeProofs.F01Aux
