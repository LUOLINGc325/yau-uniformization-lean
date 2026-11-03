import Yau.Proofs.B01FrameGram

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation BundleDbar
open LeafProofs.L14Aux

variable {r q : ℕ}

theorem embedded_curvature_gauge (E : EmbeddedFibers q) (k : EmbeddedMetric E)
    (B F : ℂ → Matrix (Fin q) (Fin r) ℂ) {O : Set ℂ} (hO : IsOpen O)
    (hB : ∀ w ∈ O, LinearMap.range (frameLinear (B w)) = E w)
    (hF : ∀ w ∈ O, LinearMap.range (frameLinear (F w)) = E w)
    (C : ℂ → Matrix (Fin r) (Fin r) ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ∞ (fun w => C w i j) O)
    (hCi : ∀ i j, ContDiffOn ℂ ∞ (fun w => (C w)⁻¹ i j) O)
    (hCF : ∀ w ∈ O, B w * C w = F w) (hdetC : ∀ w ∈ O, (C w).det ≠ 0)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => embeddedGram E k B w i j) O)
    (hpos : ∀ w ∈ O, (embeddedGram E k B w).PosDef) (z : ℂ) (hz : z ∈ O) :
    embeddedChernCurvature E k F z = (C z)ᴴ * embeddedChernCurvature E k B z * C z := by
  let H := embeddedGram E k B
  let G := embeddedGram E k F
  have hGram : ∀ w ∈ O, G w = (C w)ᴴ * H w * C w :=
    fun w hw => embeddedGram_gauge E k B F w (hB w hw) (hF w hw) (C w) (hCF w hw)
  have hdetH : ∀ w ∈ O, (H w).det ≠ 0 := fun w hw => ne_of_gt (hpos w hw).det_pos
  have hGsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun w => G w i j) O :=
    embeddedGram_gauge_smooth E k B F hB hF C hC hCF hH
  have hdetG : ∀ w ∈ O, (G w).det ≠ 0 := by
    intro w hw
    rw [hGram w hw]
    exact ne_of_gt ((hpos w hw).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hdetC w hw))))).det_pos
  have hbridgeG := scalar_curvatureMatrix_eq G O hO hGsmooth hdetG z hz
  have hbridgeH := scalar_curvatureMatrix_eq H O hO hH hdetH z hz
  let Ω : Set (ComplexVector 1) := complexOneEquiv.symm ⁻¹' O
  have hΩ : IsOpen Ω := hO.preimage complexOneEquiv.symm.continuous
  have hzΩ : complexOneEquiv z ∈ Ω := by simpa only [Ω, mem_preimage, complexOneEquiv.symm_apply_apply] using hz
  let e := complexOneEquiv.symm.toContinuousLinearEquiv
  have hHH (i j) : ContDiffOn ℝ ∞ (fun w => H (complexOneEquiv.symm w) i j) Ω :=
    (hH i j).comp (e.contDiff.restrict_scalars ℝ).contDiffOn (fun _ hw => hw)
  have hCC (i j) : ContDiffOn ℂ ∞ (fun w => C (complexOneEquiv.symm w) i j) Ω :=
    (hC i j).comp e.contDiff.contDiffOn (fun _ hw => hw)
  have hII (i j) : ContDiffOn ℂ ∞ (fun w => (C (complexOneEquiv.symm w))⁻¹ i j) Ω :=
    (hCi i j).comp e.contDiff.contDiffOn (fun _ hw => hw)
  have hcong := curvatureMatrix_congr_of_eqOn _ _ hΩ
    (show EqOn (fun w => G (complexOneEquiv.symm w))
      (fun w => (C (complexOneEquiv.symm w))ᴴ * H (complexOneEquiv.symm w) * C (complexOneEquiv.symm w)) Ω
      from fun w hw => hGram _ hw) (complexOneEquiv z) hzΩ
  have hgauge := curvatureMatrix_gauge hΩ (fun w => H (complexOneEquiv.symm w))
    (fun w => C (complexOneEquiv.symm w)) (fun w => (C (complexOneEquiv.symm w))⁻¹)
    hHH (fun w hw => hdetH _ hw) hCC hII
    (fun w hw => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdetC _ hw)))
    (complexOneEquiv z) hzΩ (0 : Fin 1) (0 : Fin 1)
  calc
    embeddedChernCurvature E k F z = curvatureMatrix (fun w => G (complexOneEquiv.symm w)) (complexOneEquiv z) 0 0 := hbridgeG.symm
    _ = curvatureMatrix (fun w => (C (complexOneEquiv.symm w))ᴴ * H (complexOneEquiv.symm w) * C (complexOneEquiv.symm w)) (complexOneEquiv z) 0 0 :=
      congrFun (congrFun hcong 0) 0
    _ = (C z)ᴴ * curvatureMatrix (fun w => H (complexOneEquiv.symm w)) (complexOneEquiv z) 0 0 * C z := by
      simpa only [complexOneEquiv.symm_apply_apply] using hgauge
    _ = _ := by rw [hbridgeH]; rfl

end Yau.Proofs.B01Aux
