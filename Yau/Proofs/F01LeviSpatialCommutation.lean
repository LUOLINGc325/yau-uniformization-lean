import Yau.Proofs.F01SpatialThirdCommutation
import Yau.Proofs.F01ComplexLeviFrobenius

/-! The derivative of the actual native Levi matrix is the Levi matrix
of the genuine spatial directional derivative, in the same Frobenius norm.
The proof uses the computed Hessian linear map and actual third-jet symmetry. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem native_levi_frobenius_contDiffOn {q : Space n → ℝ} {S : Set (Space n)}
    (hS : IsOpen S) (hq : ContDiffOn ℝ ∞ q S) :
    ContDiffOn ℝ ∞ (fun z => leviC q z) S := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ q) S := hq.fderiv_of_isOpen hS (by simp)
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ q)) S := hD.fderiv_of_isOpen hS (by simp)
  apply ((leviSecondMatrixCLM (n := n)).contDiff.comp_contDiffOn hDD).congr
  intro z hz
  exact (leviSecondMatrixCLM_eq_native ((hq.contDiffAt (hS.mem_nhds hz)).of_le (by simp))).symm

theorem leviC_spatial_direction_commute {q : Space n → ℝ} {S : Set (Space n)}
    (hS : IsOpen S) (hq : ContDiffOn ℝ ∞ q S) {x : Space n} (hx : x ∈ S) (v : Space n) :
    fderiv ℝ (fun z => leviC q z) x v = leviC (fun z => fderiv ℝ q z v) x := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ q) S := hq.fderiv_of_isOpen hS (by simp)
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ q)) S := hD.fderiv_of_isOpen hS (by simp)
  have hqv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ q z v) S := hD.clm_apply contDiffOn_const
  have hDDat := (hDD.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)
  have hcomm : fderiv ℝ (fderiv ℝ (fun z => fderiv ℝ q z v)) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ q)) x v := by
    ext a b
    exact (spatial_second_direction_commute hS hq hx v a b).trans
      (fderiv_bilinear_evaluation_const hDDat a b v)
  have hlocal : (fun z => leviC q z) =ᶠ[𝓝 x]
      (fun z => leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ q) z)) := by
    filter_upwards [hS.mem_nhds hx] with z hz
    exact (leviSecondMatrixCLM_eq_native ((hq.contDiffAt (hS.mem_nhds hz)).of_le (by simp))).symm
  have hd : HasFDerivAt (fun z => leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ q) z))
      ((leviSecondMatrixCLM (n := n)).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ q)) x)) x :=
    (leviSecondMatrixCLM (n := n)).hasFDerivAt.comp x hDDat.hasFDerivAt
  calc
    _ = fderiv ℝ (fun z => leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ q) z)) x v :=
      congrArg (fun D : Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ => D v) hlocal.fderiv_eq
    _ = leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ (fderiv ℝ q)) x v) :=
      congrArg (fun D : Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ => D v) hd.fderiv
    _ = leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ (fun z => fderiv ℝ q z v)) x) := congrArg _ hcomm.symm
    _ = _ := leviSecondMatrixCLM_eq_native ((hqv.contDiffAt (hS.mem_nhds hx)).of_le (by simp))

end Yau.NodeProofs.F01Aux
