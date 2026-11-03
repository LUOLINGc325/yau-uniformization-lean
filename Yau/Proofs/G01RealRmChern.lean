import Yau.Proofs.G01CurvatureRealification
import Yau.Proofs.G01ChernCurvature
import Yau.Proofs.G01PairingAlgebra

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem realRmInChart_eq_pairing (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (U V W Z : ComplexVector n) :
    realRmInChart h x z U V W Z =
      ∑ a, ∑ b, 2 * (complexMatrixPairing
        (hMat h x z * complexCurvatureRealDirections h x z a b) W Z).re *
          realCoord U a * realCoord V b := by
  unfold realRmInChart
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp_rw [curvature4_eq_rawReal h hs hk x z hz]
  exact raw_pairing_weighted _ W Z (realCoord U a) (realCoord V b)

/-- The all-chart real Levi-Civita tensor equals the actual mixed Chern tensor with the factor two from G. -/
theorem realRmInChart_eq_chern (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (U V W Z : ComplexVector n) :
    realRmInChart h x z U V W Z =
      2 * (∑ k, ∑ l, (∑ j, ∑ i, chernInChart h x z i j k l * W i * star (Z j)) *
        (U k * star (V l) - V k * star (U l))).re := by
  rw [realRmInChart_eq_pairing h hs hk x z hz]
  simp_rw [complexCurvatureRealDirections_eq h hs x z hz,
    Matrix.mul_sub, Matrix.mul_smul, complexMatrixPairing_sub, complexMatrixPairing_smul]
  calc
    _ = 2 * (∑ a : RIdx n, ∑ b : RIdx n,
      (realDirectionFactor a * star (realDirectionFactor b) *
          complexMatrixPairing (hMat h x z * chernF h x z a.1 b.1) W Z -
        realDirectionFactor b * star (realDirectionFactor a) *
          complexMatrixPairing (hMat h x z * chernF h x z b.1 a.1) W Z).re *
        realCoord U a * realCoord V b) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = 2 * (∑ k, ∑ l, complexMatrixPairing (hMat h x z * chernF h x z k l) W Z *
        (U k * star (V l) - V k * star (U l))).re := by
      exact congrArg (fun r : ℝ => 2 * r)
        (mixed_real_direction_contraction
          (fun k l => complexMatrixPairing (hMat h x z * chernF h x z k l) W Z) U V)
    _ = _ := by
      simp_rw [complexMatrixPairing, chernF_lower h hs x z hz]

end Yau.NodeProofs.G01Aux
