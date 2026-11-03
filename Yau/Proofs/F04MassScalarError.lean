import Yau.Proofs.F04MassErrorCofactor
import Yau.Proofs.F04DensityAdjoint

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

def massScalarError {n : ℕ} {M : ComplexManifold n} (h : HermitianField M)
    (u χ : M.Carrier → ℝ) (R : ℝ) (x : M.Carrier) : ℝ :=
  laplacian h (fun y => χ y * massCutoff u R y) x - massCutoff u R x * laplacian h χ x

theorem traceWith_add {n : ℕ} (H A B : Herm n) :
    traceWith H (A + B) = traceWith H A + traceWith H B := by
  simp only [traceWith, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem massScalarError_eq_trace {n : ℕ} {M : ComplexManifold n} (h : HermitianField M)
    {u χ : M.Carrier → ℝ} (hu : SmoothFn u) (hχ : SmoothFn χ) (R : ℝ) (x : M.Carrier) :
    massScalarError h u χ R x = traceWith (gMat h x) (massProductError u χ R x) := by
  unfold massScalarError laplacian
  rw [massProductError_identity hu hχ R x, traceWith_add, Proofs.F02Aux.traceWith_real_smul]
  ring

theorem massScalarError_smooth {n : ℕ} {M : ComplexManifold n} (h : HermitianField M)
    (hh : MetricSmooth h) {u χ : M.Carrier → ℝ} (hu : SmoothFn u) (hχ : SmoothFn χ) (R : ℝ) :
    SmoothFn (massScalarError h u χ R) :=
  smoothFn_sub (Adjoint.smoothFn_laplacian h hh (smoothFn_mul hχ (massCutoff_smooth hu R)))
    (smoothFn_mul (massCutoff_smooth hu R) (Adjoint.smoothFn_laplacian h hh hχ))

theorem massScalarError_zero_of_notMem_tsupport {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (u χ : M.Carrier → ℝ) (R : ℝ) (x : M.Carrier)
    (hx : x ∉ tsupport (massCutoff u R)) : massScalarError h u χ R x = 0 := by
  have hψ : x ∉ tsupport (fun y => χ y * massCutoff u R y) :=
    fun hh => hx (tsupport_mul_subset_right hh)
  rw [massScalarError, laplacian_zero_of_notMem_tsupport h _ hψ,
    image_eq_zero_of_notMem_tsupport hx, zero_mul, sub_self]

theorem massScalarError_compact {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : HermitianField X.manifold) (u χ : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {R : ℝ} (hR : 0 < R) : HasCompactSupport (massScalarError h u χ R) := by
  apply HasCompactSupport.of_support_subset_isCompact (massCutoff_compact X o u hu hR)
  intro x hx
  by_contra hh
  exact hx (massScalarError_zero_of_notMem_tsupport h u χ R x hh)

end Yau.F04Proof
