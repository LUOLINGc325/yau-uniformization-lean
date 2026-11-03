import Yau.Proofs.C05HarnackFrameIdentitiesAlgebra
import Yau.Proofs.C05ScalarHarnackScaling

/-! The original matrix Harnack inequality and its same-frame scalar identities. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05HarnackFrameIdentitiesAux
open Yau Yau.Blueprint Yau.Proofs.C04Aux Yau.Proofs.C05Aux Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

def sliceHarnackMatrix (k : HermitianField M) (κ : ℝ) (x : M.Carrier) :
    Matrix (Fin n) (Fin n) ℂ :=
  levi (scalarCurvature k) x + ricci k x * (gMat k x)⁻¹ * ricci k x + (κ:ℂ) • ricci k x

def sliceHarnackLeading (k : HermitianField M) (κ : ℝ) (x : M.Carrier) : ℝ :=
  3*ricciLeviPairing k (scalarCurvature k) x+2*ricciCube k x+
    κ*ricciNormSq k x-κ^2*scalarCurvature k x

theorem sliceHarnackMatrix_trace (k : HermitianField M) (κ : ℝ) (x : M.Carrier) :
    traceWith (gMat k x) (sliceHarnackMatrix k κ x)=scalarHarnackSource k κ x := by
  simp only [sliceHarnackMatrix,scalarHarnackSource,laplacian,ricciNormSq,scalarCurvature,
    traceWith,Matrix.mul_add,Matrix.trace_add,Complex.add_re,Matrix.mul_smul,
    Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

theorem sliceHarnackMatrix_scaleField (R : ℝ) (hR : 0 < R) (k : HermitianField M)
    (hs : SmoothFn (scalarCurvature k)) (κ : ℝ) (x : M.Carrier) :
    sliceHarnackMatrix (scaleField R hR k) (R⁻¹*κ) x =
      ((R⁻¹:ℝ):ℂ) • sliceHarnackMatrix k κ x := by
  have hsc : scalarCurvature (scaleField R hR k) = fun y => R⁻¹*scalarCurvature k y := by
    funext y
    exact scalar_scaleField R hR k y
  have hg : (gMat k x).PosDef :=
    L18Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  unfold sliceHarnackMatrix
  rw [hsc,levi_const_mul _ hs,gMat_scaleField,ricci_scaleField,
    inverse_real_smul R hR _ hg]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_add,smul_smul,Complex.ofReal_inv,
    Complex.ofReal_mul]

theorem sliceHarnackMatrix_flow_posSemidef (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (x : Pt X) :
    (sliceHarnackMatrix (scaleField R hR (h t)) (t*R)⁻¹ x).PosSemidef := by
  have hd : Matrix.of (fun a b => deriv (fun s => ricci (h s) x a b) t) =
      levi (scalarCurvature (h t)) x := by
    ext a b
    exact (ricci_hasDerivAt_scalar_levi o h U P ρ hf x ht a b).deriv
  have H := hH.2.2.2.1 x t ht
  rw [hd] at H
  have H0 : (sliceHarnackMatrix (h t) t⁻¹ x).PosSemidef := H
  have hs := spaceSlice_smoothFn (localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf) ht
  rw [mul_inv_rev,sliceHarnackMatrix_scaleField R hR (h t) hs]
  exact H0.smul (by exact_mod_cast (inv_nonneg.mpr hR.le))

theorem sliceHarnackMatrix_frame_posSemidef (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (t R : ℝ) (ht : 0 < t) (hR : 0 < R) (x : Pt X)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    (Wᴴ*sliceHarnackMatrix (scaleField R hR (h t)) (t*R)⁻¹ x*W).PosSemidef := by
  exact (sliceHarnackMatrix_flow_posSemidef o h U P ρ hf hH t R ht hR x).conjTranspose_mul_mul_same W

theorem sliceHarnackMatrix_frame_shift (k : HermitianField M) (κ : ℝ) (x : M.Carrier)
    (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hdet : W.det ≠ 0) (hGram : Wᴴ*gMat k x*W=1)
    (hDiag : Wᴴ*ricci k x*W=Matrix.diagonal (fun j => (lam j:ℂ))) :
    Wᴴ*levi (scalarCurvature k) x*W = Wᴴ*sliceHarnackMatrix k κ x*W -
      Matrix.diagonal (fun j => ((lam j*(lam j+κ):ℝ):ℂ)) :=
  frame_hessian_shift (gMat k x) (ricci k x) (levi (scalarCurvature k) x) W lam κ hdet hGram hDiag

theorem sliceHarnackMatrix_frame_trace (k : HermitianField M) (κ : ℝ) (x : M.Carrier)
    (W : Matrix (Fin n) (Fin n) ℂ) (hdet : W.det ≠ 0) (hGram : Wᴴ*gMat k x*W=1) :
    (Wᴴ*sliceHarnackMatrix k κ x*W).trace.re=scalarHarnackSource k κ x := by
  rw [frame_trace (gMat k x) _ W hdet hGram]
  exact sliceHarnackMatrix_trace k κ x

theorem sliceHarnackLeading_frame (k : HermitianField M) (κ : ℝ) (x : M.Carrier)
    (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hdet : W.det ≠ 0) (hGram : Wᴴ*gMat k x*W=1)
    (hDiag : Wᴴ*ricci k x*W=Matrix.diagonal (fun j => (lam j:ℂ))) :
    sliceHarnackLeading k κ x =
      diagonalScalarHarnackEvolution lam κ (Wᴴ*sliceHarnackMatrix k κ x*W) := by
  have H := frame_leading_identity (gMat k x) (ricci k x) (levi (scalarCurvature k) x)
    W lam κ hdet hGram hDiag
  simpa only [sliceHarnackLeading,sliceHarnackMatrix,ricciLeviPairing,ricciCube,
    ricciNormSq,scalarCurvature,traceWith,Matrix.mul_assoc] using H

end Yau.Proofs.C05HarnackFrameIdentitiesAux
