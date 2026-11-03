import Yau.Proofs.C03ChernGaugeGeometry

/-! The intrinsic Chern bisectional contraction is preserved by the actual
holomorphic local isometry, including the true Jacobian on both vectors. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.LeafProofs L12Aux L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem bisectionalForm_pullback
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn)) (ks : MetricSmooth k)
    (h : HermitianField M) (hs : MetricSmooth h)
    {O : Set (ComplexVector n)} (hO : IsOpen O) {Φ : ComplexVector n → M.Carrier}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O)
    (hbij : ∀ z ∈ O, Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ z))
    (heq : ∀ (z : (ComplexEuclideanManifold n hn).Carrier), z ∈ O →
      ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v))
    {z : (ComplexEuclideanManifold n hn).Carrier} (hz : z ∈ O) (u a : ComplexVector n) :
    bisectionalForm k z u a =
      bisectionalForm h (Φ z)
        (tangentCoords (Φ z) (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z u))
        (tangentCoords (Φ z) (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z a)) := by
  let c := Φ z
  let L := fderiv ℂ (fun w => chartPt c (Φ w)) z
  let J := linearMatrix L
  let F := BundleDbar.curvatureMatrix (hMat h c) (chartPt c c)
  have hzC : z ∈ O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source := by
    refine ⟨hz, ?_⟩
    simpa only [Set.mem_preimage, extChartAt_source] using mem_chart_source (ComplexVector n) c
  have hΦd := (hΦ.contMDiffAt (hO.mem_nhds hz)).mdifferentiableAt (by simp)
  have hJ (v : ComplexVector n) :
      J *ᵥ WithLp.ofLp v =
        WithLp.ofLp (tangentCoords c (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z v)) := by
    rw [linearMatrix_mulVec]
    congr 1
    exact (congrArg (fun T : ComplexVector n →L[ℂ] ComplexVector n => T v)
      (coordinateDifferential_eq_fderiv Φ c z hΦd hzC.2)).symm.trans
        (coordinateDifferential_apply Φ c z v)
  have hc : BundleDbar.curvatureMatrix (fun w => gMat k w) z =
      (fun i j => Jᴴ * (∑ p, ∑ q, (J p i * star (J q j)) • F p q) * J) := by
    funext i j
    exact source_curvatureMatrix_transform hn k h hs hO hΦ hbij heq c hzC i j
  have hflat : hMat k z = (fun w : ComplexVector n => gMat k w) := by
    funext w
    exact flat_hMat_eq_gMat hn k z w
  rw [bisectionalForm_eq_matrixCurvatureQuadratic k ks z,
    bisectionalForm_eq_matrixCurvatureQuadratic h hs (Φ z), hflat, flat_chartPt hn,
    hc, matrixCurvatureQuadratic_gauge, hJ u, hJ a]

end Yau.Proofs.C03Aux.ChernGauge
