import Yau.Proofs.C02HolomorphicManifoldCriterion
import Yau.Proofs.C02NormalComplexStructure

/-! The corrected normal map is holomorphic on the original manifold.
All target coordinates are genuine charts of that same manifold. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normal_composition_contMDiffOn
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    {K : ℝ} (hK : 0 ≤ K)
    (hRm : ∀ y, inducedDistance g.form p y ≤ 1 → curvatureJetNorm g.form 0 y ≤ K)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {G : ComplexVector n → ComplexVector n} (hG : ContDiffOn ℝ ∞ G O)
    (hRange : ∀ z ∈ O, ‖G z‖ ≤ radialGaugeRadius K)
    (hInner : ∀ z ∈ O, ∀ v,
      fderiv ℝ G z (Complex.I • v) =
        normalGaugeComplex g p U hU (G z) (fderiv ℝ G z v)) :
    ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (normalRealMap g p U ∘ G) O := by
  letI := manifold_realSmooth M
  have hContinuous : ContinuousOn (normalRealMap g p U ∘ G) O :=
    (normalRealMap_smooth g p U hU).continuous.comp_continuousOn hG.continuousOn
  apply contMDiffOn_of_real_CauchyRiemann_charts hO hContinuous
  · intro c z hz
    have hD : DifferentiableAt ℝ G z :=
      (hG.contDiffAt (hO.mem_nhds hz.1)).differentiableAt (by simp)
    have hChart : IsOpen ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) :=
      (chartAt (ComplexVector n) c).open_source.preimage
        (normalRealMap_smooth g p U hU).continuous
    exact ((normalCoordinateMap_smooth g p U hU c).contDiffAt
      (hChart.mem_nhds hz.2)).differentiableAt (by simp) |>.comp z hD
  · intro c z hz v
    have hD : DifferentiableAt ℝ G z :=
      (hG.contDiffAt (hO.mem_nhds hz.1)).differentiableAt (by simp)
    have hChart : IsOpen ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) :=
      (chartAt (ComplexVector n) c).open_source.preimage
        (normalRealMap_smooth g p U hU).continuous
    have hN : DifferentiableAt ℝ (normalCoordinateMap g p U c) (G z) :=
      ((normalCoordinateMap_smooth g p U hU c).contDiffAt
        (hChart.mem_nhds hz.2)).differentiableAt (by simp)
    change fderiv ℝ (normalCoordinateMap g p U c ∘ G) z (Complex.I • v) =
      Complex.I • fderiv ℝ (normalCoordinateMap g p U c ∘ G) z v
    rw [fderiv_comp z hN hD, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hInner z hz.1]
    exact normalGaugeComplex_intertwines g p U hU hK hRm c (G z)
      (fderiv ℝ G z v) (hRange z hz.1) hz.2

end Yau.Blueprint.C02Proof
