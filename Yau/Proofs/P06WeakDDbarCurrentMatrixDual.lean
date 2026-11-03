import Yau.Proofs.P06WeakLeviMatrixTests

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexOrder

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux

/-- The matrix test's coordinate dual is the genuine distributional
adjoint of the classical Levi matrix. -/
theorem integral_leviMatrixTestDual_classical {n : ℕ} {O : Set (ComplexVector n)}
    (hO : IsOpen O) (u : ComplexVector n → ℝ) (hu : ContDiffOn ℝ ∞ u O)
    (B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hBH : ∀ z, (B z).IsHermitian)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun z => B z i j))
    (hcB : ∀ i j, HasCompactSupport (fun z => B z i j))
    (hBO : ∀ i j, tsupport (fun z => B z i j) ⊆ O) :
    (∫ z, u z * leviMatrixTestDual B z ∂lebesgueC n) =
      ∫ z, (Matrix.trace (leviC u z * B z)).re ∂lebesgueC n := by
  have : (lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]; infer_instance
  have hreg := hermitianTestCoefficients_regular B hB hcB hBO
  rw [leviMatrixTestDual_integral hO u hu.continuousOn B hreg]
  simp_rw [integral_leviDirection_test hO (hreg _).1 (hreg _).2.1 (hreg _).2.2 hu]
  rw [← integral_finsetSum _ (fun p _ =>
    integrable_compactTest_mul (lebesgueC n) hO (hreg p).1.continuous
      (hreg p).2.1 (hreg p).2.2
      (leviDirection_contDiffOn hO hu (hermitianTestVectors n p)).continuousOn)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← trace_rankOne_family, hermitianTestDecomposition (B z) (hBH z)]

end Yau.NodeProofs.P06Aux.WeakCurrent
