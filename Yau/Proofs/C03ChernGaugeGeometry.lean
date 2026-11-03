import Yau.Proofs.C03ChernGaugeJacobian
import Yau.Proofs.C03ChernGaugeMatrix
import Yau.Proofs.C03ChernGaugeChernTensor

/-! Actual local Chern naturality for the source matrix gMat k and the true
holomorphic differential of the given map. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux.ChernGauge

open Yau Yau.Blueprint Yau.LeafProofs L12Aux L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem source_curvatureMatrix_transform
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn))
    (h : HermitianField M) (hs : MetricSmooth h)
    {O : Set (ComplexVector n)} (hO : IsOpen O) {Φ : ComplexVector n → M.Carrier}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O)
    (hbij : ∀ z ∈ O, Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ z))
    (heq : ∀ (z : (ComplexEuclideanManifold n hn).Carrier), z ∈ O →
      ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v))
    (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source) (i j : Fin n) :
    BundleDbar.curvatureMatrix (fun w => gMat k w) z i j =
      (linearMatrix (fderiv ℂ (fun w => chartPt c (Φ w)) z))ᴴ *
        (∑ p, ∑ q,
          (fderiv ℂ (fun w => chartPt c (Φ w)) z (stdVec i) p *
            star (fderiv ℂ (fun w => chartPt c (Φ w)) z (stdVec j) q)) •
          BundleDbar.curvatureMatrix (hMat h c) (chartPt c (Φ z)) p q) *
        linearMatrix (fderiv ℂ (fun w => chartPt c (Φ w)) z) := by
  have hOc := coordinate_open hO hΦ.continuousOn c
  have hf := coordinate_holomorphic hΦ c
  apply curvatureMatrix_of_local_congruence hOc
    (isOpen_extChartAt_target (I := ComplexModel n) c)
    (fun w => gMat k w) (hMat h c) (fun w => chartPt c (Φ w))
    (fun w => linearMatrix (fderiv ℂ (fun p => chartPt c (Φ p)) w))
    (hMat_contDiffOn_of_metricSmooth h hs c)
    (fun w hw => ((L12Aux.hMat_posDef h c w hw).isUnit.map Matrix.detMonoidHom).ne_zero)
    hf (fun w hw => (extChartAt (ComplexModel n) c).map_source hw.2)
    (jacobian_holomorphic hOc hf) _ _ z hz i j
  · intro w hw
    exact linearMatrix_det_ne_zero _ (jacobian_injective Φ c w
      ((hΦ.contMDiffAt (hO.mem_nhds hw.1)).mdifferentiableAt (by simp)) hw.2 (hbij w hw.1))
  · intro w hw
    exact source_gMat_congruence hn k h Φ w c
      ((hΦ.contMDiffAt (hO.mem_nhds hw.1)).mdifferentiableAt (by simp)) hw.2 (heq w hw.1)

end Yau.Proofs.C03Aux.ChernGauge
