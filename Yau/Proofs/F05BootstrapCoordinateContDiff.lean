import Yau.LeafProofs.L16ChartOperatorAlgebra
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Finite real-frame component regularity determines regularity of the
actual covector and bilinear fields in their operator norms. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_covector_contDiff_of_components {k : ℕ∞ω} {Q : Set (Point n)}
    {G : Point n → Space n →L[ℝ] ℝ}
    (hG : ∀ i, ContDiffOn ℝ k (fun z => G z (realVec i)) Q) : ContDiffOn ℝ k G Q := by
  apply contDiffOn_clm_apply.mpr
  intro v
  have hSum : ContDiffOn ℝ k (fun z => ∑ i,realCoord v i*G z (realVec i)) Q :=
    ContDiffOn.sum (fun i (_ : i ∈ (Finset.univ : Finset (RIdx n))) =>
      (contDiffOn_const : ContDiffOn ℝ k (fun _ : Point n => realCoord v i) Q).mul (hG i))
  apply hSum.congr
  intro z hz
  exact realCovector_coordinate_expansion (G z) v

theorem F05_bilinear_contDiff_of_components {k : ℕ∞ω} {Q : Set (Point n)}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hH : ∀ i j, ContDiffOn ℝ k (fun z => H z (realVec i) (realVec j)) Q) :
    ContDiffOn ℝ k H Q := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have hSum : ContDiffOn ℝ k (fun z => ∑ i,∑ j,realCoord v i*realCoord w j*H z (realVec i) (realVec j)) Q :=
    ContDiffOn.sum (fun i (_ : i ∈ (Finset.univ : Finset (RIdx n))) =>
      ContDiffOn.sum (fun j (_ : j ∈ (Finset.univ : Finset (RIdx n))) =>
        (contDiffOn_const : ContDiffOn ℝ k (fun _ : Point n => realCoord v i*realCoord w j) Q).mul (hH i j)))
  apply hSum.congr
  intro z hz
  exact realBilinear_coordinate_expansion (H z) v w

end Yau.Proofs.F05Aux
