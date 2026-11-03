import Yau.Proofs.F05SymbolNormalization

/-! The original centered-chart Laplacian in any actual holomorphic chart,
under pointwise C2 regularity rather than a global smoothness hypothesis. -/

open Set
open scoped Topology ContDiff Manifold Matrix
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_backgroundChart_hMat (h : HermitianField M) (x : M.Carrier)
    {z : Space n} (hz : z ∈ chartTarget x) :
    pullbackMatrix h (chartInv x) z = hMat h x z := by
  have hRound : chartPt x (chartInv x z) = z :=
    (extChartAt (ComplexModel n) x).right_inv hz
  ext a b
  change (h (chartInv x z)).toFun
    (mfderiv (ComplexModel n) (ComplexModel n) (chartInv x) z (stdVec a))
    (mfderiv (ComplexModel n) (ComplexModel n) (chartInv x) z (stdVec b)) =
    (h (chartInv x z)).toFun
    (mfderiv (ComplexModel n) (ComplexModel n) (chartInv x)
      (chartPt x (chartInv x z)) (stdVec a))
    (mfderiv (ComplexModel n) (ComplexModel n) (chartInv x)
      (chartPt x (chartInv x z)) (stdVec b))
  rw [hRound]

theorem F05_laplacian_local_chart (h : HermitianField M) (x : M.Carrier)
    (f : M.Carrier → ℝ) {z : Space n} (hz : z ∈ chartTarget x)
    (hf : ContDiffAt ℝ 2 (inChart (chartInv x z) f)
      (chartPt (chartInv x z) (chartInv x z))) :
    laplacian h f (chartInv x z) =
      ∑ a, ∑ b, baseA h x z a b *
        fderiv ℝ (fderiv ℝ (inChart x f)) z (realVec a) (realVec b) := by
  let e : OpenPartialHomeomorph (Space n) M.Carrier := (chartAt (Space n) x).symm
  have hInv : (e : Space n → M.Carrier) = chartInv x := by
    funext y
    simp [e,chartInv,ComplexModel]
  have he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt_symm (I := ComplexModel n) (x := x))
  have hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt (I := ComplexModel n) (x := x))
  have hzE : z ∈ e.source := by simpa [e,chartTarget,ComplexModel] using hz
  have hfE : ContDiffAt ℝ 2 (inChart (e z) f) (chartPt (e z) (e z)) := by
    rwa [hInv]
  have hCalc := laplacian_eq_backgroundChart_scalarSymbol h e he hei f hzE hfE
  rw [hInv,F05_backgroundChart_hMat h x hz] at hCalc
  unfold inChart
  simpa only [realHessianContraction,← F05_baseA_eq_scalarSymbol h x hz] using hCalc

end Yau.Proofs.F05Aux
