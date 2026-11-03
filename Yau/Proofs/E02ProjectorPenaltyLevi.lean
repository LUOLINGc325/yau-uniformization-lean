import Yau.Proofs.E02ProjectorHessian
import Yau.Proofs.E02LogGramSecond

open Matrix Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def projectorTraceCLM {m : ℕ} (P₀ : Herm m) : Herm m →L[ℝ] ℝ :=
  (matrixTraceRealCLM m).comp (rectMulCLM m m m P₀)

theorem projectorPenalty_second_fderiv {n m : ℕ} (P₀ : Herm m) (M Y Z : Rect n m)
    (hP : ContDiffAt ℝ 2 (rowProjector (n := n) (m := m)) M) :
    fderiv ℝ (fderiv ℝ (projectorPenalty (n := n) P₀)) M Y Z =
      -(Matrix.trace (P₀*fderiv ℝ (fderiv ℝ rowProjector) M Y Z)).re := by
  let L : Herm m →L[ℝ] ℝ := projectorTraceCLM P₀
  have hFirst : fderiv ℝ (projectorPenalty (n := n) P₀) =
      -(fderiv ℝ (L ∘ rowProjector (n := n) (m := m))) := by
    funext N
    exact fderiv_const_sub (n : ℝ)
  rw [hFirst]
  have hG : ContDiffAt ℝ 2 (L ∘ rowProjector (n := n) (m := m)) M :=
    hP.continuousLinearMap_comp L
  have hNeg : HasFDerivAt (-(fderiv ℝ (L ∘ rowProjector (n := n) (m := m))))
      (-fderiv ℝ (fderiv ℝ (L ∘ rowProjector)) M) M :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.neg
  have hVal := congrArg (fun A : Rect n m →L[ℝ] Rect n m →L[ℝ] ℝ => A Y Z) hNeg.fderiv
  calc
    _ = -fderiv ℝ (fderiv ℝ (L ∘ rowProjector)) M Y Z := hVal
    _ = _ := by
      exact congrArg (fun r : ℝ => -r) (second_fderiv_continuousLinearMap_comp hP L Y Z)

/-- Exact Levi of the actual real projector penalty, computed by the
original Frechet derivatives. Its constant-one upper bound is a separate
finite-dimensional trace-order calculation. -/
theorem projectorPenalty_rectLevi {n m : ℕ} (P₀ : Herm m) (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef) (hP : ContDiffAt ℝ 2 (rowProjector (n := n) (m := m)) M)
    (hInv : ∀ᶠ N in 𝓝 M, DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) N) :
    rectLevi (projectorPenalty (n := n) P₀) M Z =
      (Matrix.trace (P₀*(projectorTangent M Z*(projectorTangent M Z)ᴴ-
        (projectorTangent M Z)ᴴ*projectorTangent M Z))).re := by
  have hMix := rowProjector_mixed_real_hessian M Z hM hP hInv
  have hRealScalar (A : Herm m) : (1/4 : ℝ) • A = (1/4 : ℂ) • A := by
    ext i j
    simp [Matrix.smul_apply,Complex.real_smul]
  have hRealMix : (1/4 : ℝ) • (fderiv ℝ (fderiv ℝ rowProjector) M Z Z+
      fderiv ℝ (fderiv ℝ rowProjector) M (Complex.I • Z) (Complex.I • Z)) =
      (projectorTangent M Z)ᴴ*projectorTangent M Z-
        projectorTangent M Z*(projectorTangent M Z)ᴴ := by
    rw [hRealScalar]
    exact hMix
  have hTrace := congrArg (projectorTraceCLM P₀) hRealMix
  simp only [map_smul,map_add,smul_eq_mul] at hTrace
  change (1/4 : ℝ)*((Matrix.trace (P₀*fderiv ℝ (fderiv ℝ rowProjector) M Z Z)).re+
      (Matrix.trace (P₀*fderiv ℝ (fderiv ℝ rowProjector) M (Complex.I • Z) (Complex.I • Z))).re) =
      (Matrix.trace (P₀*((projectorTangent M Z)ᴴ*projectorTangent M Z-
        projectorTangent M Z*(projectorTangent M Z)ᴴ))).re at hTrace
  rw [rectLevi,projectorPenalty_second_fderiv P₀ M Z Z hP,
    projectorPenalty_second_fderiv P₀ M (Complex.I • Z) (Complex.I • Z) hP]
  simp only [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re] at hTrace ⊢
  linarith

end Yau.NodeProofs.E02Aux
