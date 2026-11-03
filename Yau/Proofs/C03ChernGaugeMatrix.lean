import Yau.Proofs.C03ChernGaugeInverse
import Yau.LeafProofs.L14Gauge

/-! Computed Chern curvature of an actual local holomorphic congruence.
The inverse gauge is the matrix inverse, constructed from nonzero determinant. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.BundleDbar Yau.LeafProofs.L14Aux

theorem curvatureMatrix_of_local_congruence {n r : ℕ}
    {O U : Set (ComplexVector n)} (hO : IsOpen O) (hU : IsOpen U)
    (H₀ H₁ : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (f : ComplexVector n → ComplexVector n)
    (J : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ α β, ContDiffOn ℝ ∞ (fun w => H₁ w α β) U)
    (hdetH : ∀ w ∈ U, (H₁ w).det ≠ 0)
    (hf : ContDiffOn ℂ ∞ f O) (hfU : Set.MapsTo f O U)
    (hJ : ∀ α β, ContDiffOn ℂ ∞ (fun w => J w α β) O)
    (hdetJ : ∀ w ∈ O, (J w).det ≠ 0)
    (heq : Set.EqOn H₀ (fun w => (J w)ᴴ * H₁ (f w) * J w) O)
    (z : ComplexVector n) (hz : z ∈ O) (i j : Fin n) :
    curvatureMatrix H₀ z i j =
      (J z)ᴴ * (∑ p, ∑ q,
        (fderiv ℂ f z (stdVec i) p * star (fderiv ℂ f z (stdVec j) q)) •
          curvatureMatrix H₁ (f z) p q) * J z := by
  rw [curvatureMatrix_congr_of_eqOn H₀ _ hO heq z hz]
  exact curvatureMatrix_holomorphic_change hO hU H₁ f J (fun w => (J w)⁻¹)
    hH hdetH hf hfU hJ (matrix_inv_contDiffOn_complex hJ hdetJ)
    (fun w hw => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdetJ w hw))) z hz i j

end Yau.Proofs.C03Aux.ChernGauge
