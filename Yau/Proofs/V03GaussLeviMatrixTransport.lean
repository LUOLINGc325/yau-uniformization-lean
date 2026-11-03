import Yau.Proofs.V03GaussTwoFormTransport
import Yau.Proofs.V03LeviTwoFormRecovery

/-! Every entry of the actual Gauss Levi matrix transforms by the
original cotangent transition matrix, obtained from native two-form covariance. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem gaussLeviMatrix_chart_change {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x x' : M.Carrier) {y : CotangentPoint M}
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') :
    leviMatrix (gaussPotential G x) (cotangentChart x y) cotangentDir =
      (cotangentTransition x x' y)ᴴ *
        leviMatrix (gaussPotential G x') (cotangentChart x' y) cotangentDir *
          cotangentTransition x x' y := by
  have hz := cotangentChart_mapsTo x hy
  have hb : chartInv x (cotangentChart x y).1 = y.1 := (extChartAt (ComplexModel n) x).left_inv hy
  have hΩ := gaussTwoForm_chart_change hG x x' hz (by rw [hb]; exact hy')
  rw [cotangentChart_left_inv x hy] at hΩ
  have hf := (gaussPotential_contDiffAt hG x hz).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hg := (gaussPotential_contDiffAt hG x' (cotangentChart_mapsTo x' hy')).of_le
    (show (2 : ℕ∞ω) ≤ ∞ by simp)
  let A := fderiv ℂ (fun w => cotangentChart x' (cotangentChartInv x w)) (cotangentChart x y)
  ext a b
  change wirt (fun w => wirtBar (fun w' => (gaussPotential G x w' : ℂ)) w (cotangentDir a))
    (cotangentChart x y) (cotangentDir b) = _
  rw [scalarLevi_mixed_eq_of_twoForm_eq hf hg A hΩ]
  have hu := cotangentVectorOfCoords_coordsVector (A (cotangentDir a))
  have hv := cotangentVectorOfCoords_coordsVector (A (cotangentDir b))
  rw [← hu, ← hv, cotangent_levi_contraction hg, Matrix.mul_assoc]
  rfl

end Yau.Blueprint.V03Proof
