import Yau.Proofs.U02FirstExit

/-! The straight segment on the indicated immersed chart sheet cannot
escape a fixed initial metric ball when its actual length budget is small. -/

open scoped Manifold Topology ContDiff
open Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint
open Yau.LeafProofs.L12Aux

theorem unitaryChart_short_segment {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (h : HermitianField M) (p x : M.Carrier)
    (Phi : ComplexVector n → M.Carrier) {r c C ell R : ℝ}
    (hc : UnitaryChart h p Phi r c C) (hC : 0 < C) (hell : 0 < ell) (hR : 0 < R)
    (hmetric : ∀ y, inducedDistance g.form x y ≤ R →
      HermLE (((ell ^ 2 : ℝ) : ℂ) • gMat g.form y) (gMat h y))
    {u v : ComplexVector n} (hu : u ∈ ball 0 r) (hv : v ∈ ball 0 r)
    (hstart : Phi u = x)
    (hshort : Real.sqrt (2 * C) / ell * ‖v - u‖ < R) :
    inducedDistance g.form x (Phi v) < R := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  let eta := ContinuousAffineMap.lineMap (R := ℝ) u v
  let gamma := Phi ∘ eta
  have heta : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 eta := by
    rw [contMDiff_iff_contDiff]
    exact eta.contDiff
  have hmap : Set.MapsTo eta (Set.Icc 0 1) (ball 0 r) := by
    change Set.Icc 0 1 ⊆ eta ⁻¹' ball 0 r
    rw [← Set.image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact (convex_ball (0 : ComplexVector n) r).segment_subset hu hv
  have hPhi := (chart_real_contMDiffOn hc.1.1).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 gamma (Set.Icc 0 1) :=
    hPhi.comp heta.contMDiffOn hmap
  have hgamma0 : gamma 0 = x := by
    simpa [gamma, eta, ContinuousAffineMap.coe_lineMap_eq] using hstart
  have hgamma1 : gamma 1 = Phi v := by
    simp [gamma, eta, ContinuousAffineMap.coe_lineMap_eq]
  rw [← hgamma1]
  apply short_path_endpoint_distance g x gamma hR (by positivity) hshort hgamma0 hgamma
  intro t ht hdist
  have hz := hmap ht
  have hpd := ((hPhi (eta t) hz).contMDiffAt (isOpen_ball.mem_nhds hz)).mdifferentiableAt
    (by simp)
  have hline : HasDerivAt eta (v - u) t := AffineMap.hasDerivAt_lineMap
  have he : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) gamma t 1 =
      mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) Phi (eta t)
        ((NormedSpace.fromTangentSpace (eta t)).symm (v - u)) := by
    rw [mfderiv_comp t hpd hline.differentiableAt.mdifferentiableAt,
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
    simp [NormedSpace.fromTangentSpace, tangentSpaceCastModel, mfld_simps]
    change (1 : ℝ) • _ = _
    exact one_smul ℝ _
  rw [he]
  exact chart_real_derivative_bound g h p Phi hc hC hell hz
    (hmetric (Phi (eta t)) hdist) (v - u)

end Yau.NodeProofs.U02Proof
