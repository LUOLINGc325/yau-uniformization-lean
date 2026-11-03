import Yau.Proofs.D02PullbackRegularity
import Yau.LeafProofs.L14Curvature

/-! The actual Chern curvature chain rule for a holomorphic map between
different base dimensions. All matrices and derivatives are computed. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.LeafProofs.L14Aux Yau.BundleDbar

theorem matrixWirt_comp_different_dim {m n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector m → ComplexVector n) (z : ComplexVector m)
    (hT : DifferentiableAt ℂ T z)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) (T z)) (i : Fin m) :
    matrixWirt (fun w => H (T w)) z i =
      ∑ p, (fderiv ℂ T z (stdVec i) p) • matrixWirt H (T z) p := by
  ext α β
  simp only [matrixWirt, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [wirt_comp_complex_differentiable T _ z (stdVec i) hT (hH α β), wirt_direction_coordinates]


theorem matrixWirtBar_comp_different_dim {m n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector m → ComplexVector n) (z : ComplexVector m)
    (hT : DifferentiableAt ℂ T z)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) (T z)) (i : Fin m) :
    matrixWirtBar (fun w => H (T w)) z i =
      ∑ p, star (fderiv ℂ T z (stdVec i) p) • matrixWirtBar H (T z) p := by
  ext α β
  simp only [matrixWirtBar, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [wirtBar_comp_complex_differentiable T _ z (stdVec i) hT (hH α β), wirtBar_direction_coordinates]


theorem chernConnectionMatrix_comp_different_dim {m n r : ℕ}
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector m → ComplexVector n) (z : ComplexVector m)
    (hT : DifferentiableAt ℂ T z)
    (hH : ∀ α β, DifferentiableAt ℝ (fun w => H w α β) (T z)) (i : Fin m) :
    chernConnectionMatrix (fun w => H (T w)) z i =
      ∑ p, (fderiv ℂ T z (stdVec i) p) • chernConnectionMatrix H (T z) p := by
  change (H (T z))⁻¹ * matrixWirt (fun w => H (T w)) z i = _
  rw [matrixWirt_comp_different_dim H T z hT hH i]
  simp only [Matrix.mul_sum, Matrix.mul_smul, chernConnectionMatrix, matrixWirt]
  rfl


theorem curvatureMatrix_comp_different_dim {m n r : ℕ}
    {O : Set (ComplexVector m)} {U : Set (ComplexVector n)} (hO : IsOpen O) (hU : IsOpen U)
    (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (T : ComplexVector m → ComplexVector n)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H w α β) U)
    (hdet : ∀ w ∈ U, (H w).det ≠ 0) (hT : ContDiffOn ℂ ∞ T O)
    (hTU : Set.MapsTo T O U) (z : ComplexVector m) (hz : z ∈ O) (i j : Fin m) :
    curvatureMatrix (fun w => H (T w)) z i j =
      ∑ p, ∑ q, (fderiv ℂ T z (stdVec i) p * star (fderiv ℂ T z (stdVec j) q)) •
        curvatureMatrix H (T z) p q := by
  let J := fun w p => fderiv ℂ T w (stdVec i) p
  let Γ := fun p w => chernConnectionMatrix H (T w) p
  have hTz : ContDiffAt ℂ ∞ T z := hT.contDiffAt (hO.mem_nhds hz)
  have hTd : DifferentiableAt ℂ T z := hTz.differentiableAt (by simp)
  have hΓd (p : Fin n) (α β : Fin r) :
      DifferentiableAt ℝ (fun w => chernConnectionMatrix H w p α β) (T z) :=
    ((chernConnectionMatrix_contDiffOn hU H hH hdet p α β).contDiffAt
      (hU.mem_nhds (hTU hz))).differentiableAt (by simp)
  have hΓcomp (p : Fin n) (α β : Fin r) : DifferentiableAt ℝ (fun w => Γ p w α β) z :=
    (hΓd p α β).comp z (hTd.restrictScalars ℝ)
  have hJd (p : Fin n) : DifferentiableAt ℂ (fun w => J w p) z := by
    have hDT : ContDiffAt ℂ ∞ (fderiv ℂ T) z := hTz.fderiv_right (m := ∞) (by simp)
    exact ((contDiffAt_piLp 2).mp (hDT.clm_apply (show ContDiffAt ℂ ∞ (fun _ : ComplexVector m => stdVec i) z from
      contDiffAt_const)) p).differentiableAt (by simp)
  have hEq : (fun w => chernConnectionMatrix (fun t => H (T t)) w i) =ᶠ[𝓝 z]
      (fun w => ∑ p, J w p • Γ p w) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    apply chernConnectionMatrix_comp_different_dim H T w
      ((hT.contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))
    intro α β
    exact ((hH α β).contDiffAt (hU.mem_nhds (hTU hw))).differentiableAt (by simp)
  have hbar : matrixWirtBar (fun w => chernConnectionMatrix (fun t => H (T t)) w i) z j =
      ∑ p, ∑ q, (J z p * star (fderiv ℂ T z (stdVec j) q)) •
        matrixWirtBar (fun w => chernConnectionMatrix H w p) (T z) q := by
    rw [matrixWirtBar_congr_of_eventuallyEq _ _ z hEq j]
    rw [matrixWirtBar_sum (fun p w => J w p • Γ p w) z
      (fun p α β => ((hJd p).restrictScalars ℝ).mul (hΓcomp p α β)) j]
    apply Finset.sum_congr rfl
    intro p _
    rw [matrixWirtBar_smul (fun w => J w p) (Γ p) z ((hJd p).restrictScalars ℝ)
      (hΓcomp p) j, wirtBar_eq_zero_of_complex_differentiable _ z (stdVec j) (hJd p),
      zero_smul, zero_add]
    rw [matrixWirtBar_comp_different_dim (fun w => chernConnectionMatrix H w p) T z hTd (hΓd p) j]
    simp only [Finset.smul_sum, smul_smul]
  change -(H (T z) * matrixWirtBar (fun w => chernConnectionMatrix (fun t => H (T t)) w i) z j) = _
  rw [hbar]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Finset.sum_neg_distrib, smul_neg,
    curvatureMatrix, matrixWirtBar]
  rfl


end Yau.NodeProofs.D02Aux
