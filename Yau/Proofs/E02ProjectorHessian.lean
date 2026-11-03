import Yau.Proofs.E02SecondPostcomp
import Yau.Proofs.E02ProjectorSecond
import Yau.LeafProofs.L18

open Matrix Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem matrix_entry_second_fderiv {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n m : ℕ} {F : D → Rect n m} {x : D} (hF : ContDiffAt ℝ 2 F x)
    (i : Fin n) (j : Fin m) (v w : D) :
    fderiv ℝ (fderiv ℝ (fun y => F y i j)) x v w =
      fderiv ℝ (fderiv ℝ F) x v w i j :=
  second_fderiv_continuousLinearMap_comp hF (rectEntryCLM n m i j) v w

/-- The original nested Wirtinger derivative of a C² matrix entry is
the quarter-sum of the two actual real Hessian entries. -/
theorem matrix_entry_wirt_wirtBar_eq_hessian {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℂ D]
    {n m : ℕ} {F : D → Rect n m} {x : D} (hF : ContDiffAt ℝ 2 F x)
    (i : Fin n) (j : Fin m) (v : D) :
    wirt (fun y => wirtBar (fun z => F z i j) y v) x v =
      (1/4 : ℂ)*(fderiv ℝ (fderiv ℝ F) x v v i j+
        fderiv ℝ (fderiv ℝ F) x (Complex.I • v) (Complex.I • v) i j) := by
  have hEntry : ContDiffAt ℝ 2 (fun y => F y i j) x :=
    hF.continuousLinearMap_comp (rectEntryCLM n m i j)
  have hD := (hEntry.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hSym := hEntry.isSymmSndFDerivAt (by norm_num)
  rw [Yau.LeafProofs.L18Aux.wirt_wirtBar_eq_secondFDeriv hD v v,
    hSym v (Complex.I • v),sub_self,mul_zero,add_zero,
    matrix_entry_second_fderiv hF i j v v,
    matrix_entry_second_fderiv hF i j (Complex.I • v) (Complex.I • v)]

/-- The genuine matrix-valued real Hessian average of the actual
projector agrees with its already computed nested Wirtinger derivative. -/
theorem rowProjector_mixed_real_hessian {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef) (hP : ContDiffAt ℝ 2 (rowProjector (n := n) (m := m)) M)
    (hInv : ∀ᶠ N in 𝓝 M, DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) N) :
    (1/4 : ℂ) • (fderiv ℝ (fderiv ℝ rowProjector) M Z Z+
      fderiv ℝ (fderiv ℝ rowProjector) M (Complex.I • Z) (Complex.I • Z)) =
      (projectorTangent M Z)ᴴ*projectorTangent M Z-
        projectorTangent M Z*(projectorTangent M Z)ᴴ := by
  apply Matrix.ext
  intro i j
  have h := (matrix_entry_wirt_wirtBar_eq_hessian hP i j Z).symm.trans
    (rowProjector_wirt_wirtBar_of_inverseGram M Z hM hInv i j)
  convert h using 1
  rfl

end Yau.NodeProofs.E02Aux
