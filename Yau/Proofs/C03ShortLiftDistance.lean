import Yau.Proofs.C03ShortLiftSheet
import Yau.Proofs.C03ShortLiftMapDistance
import Yau.Proofs.C03ShortLiftLengthCongr

/-! The same actual holomorphic sheet has the required intrinsic source-distance bound. -/
noncomputable section
open scoped Manifold Topology ContDiff
open Set
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Yau.LeafProofs L12Aux C07RadialCurveAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}
local instance (hn : 1 ≤ n) : NormedAddCommGroup (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℝ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℂ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))
local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n =>
      WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

theorem section_source_distance
    (k : HermitianField M) (hs : MetricSmooth k)
    (Phi : ComplexVector n → M.Carrier) (r : ℝ)
    (hPhi : IsLocalBiholomorphism Phi r)
    (ctarget : M.Carrier) (w0 : ComplexVector n) (delta L : ℝ)
    (hL : 0 < L) (hW : Metric.ball w0 delta ⊆ chartTarget ctarget)
    (hp0 : Phi 0 = chartInv ctarget w0)
    (hG : ∀ q ∈ Metric.ball w0 delta, ∀ v : ComplexVector n,
      realMetricInChart k ctarget q v v ≤ L ^ 2 * ‖v‖ ^ 2)
    (sigma : ComplexVector n → ComplexVector n)
    (hsigma0 : sigma w0 = 0)
    (hsmooth : ContDiffOn ℂ ∞ sigma (Metric.ball w0 delta))
    (hmaps : MapsTo sigma (Metric.ball w0 delta) (Metric.ball 0 r))
    (hright : ∀ w ∈ Metric.ball w0 delta, Phi (sigma w) = chartInv ctarget w)
    (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn))
    (hks : MetricSmooth ks)
    (heq : ∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
      (ks z).toFun u v = (k (Phi z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z v)) :
    ∀ w ∈ Metric.ball w0 delta,
      inducedDistance ks 0 (sigma w) ≤ L * ‖w - w0‖ := by
  intro w hw
  let z := w - w0
  have hz : ‖z‖ < delta := by simpa only [z, Metric.mem_ball, dist_eq_norm] using hw
  let F : ComplexVector n → ComplexVector n := fun q => sigma (w0 + q)
  have hF0 : F 0 = 0 := by simpa only [F, add_zero] using hsigma0
  have hFs : ContDiffOn ℂ ∞ F (Metric.ball 0 delta) :=
    hsmooth.comp (contDiff_const.add contDiff_id).contDiffOn
      (fun q hq => shift_ball_mem w0 q delta hq)
  have hF : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ F (Metric.ball 0 delta) :=
    hFs.contMDiffOn
  let source := radialIntegrable (M := ComplexEuclideanManifold n hn) hks hF0 hF hz
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (source.1 t : ComplexVector n) ∈ Metric.ball 0 r := by
    intro t ht
    change radialPath (M := ComplexEuclideanManifold n hn) F z t ∈ Metric.ball 0 r
    rw [radialPath_eq (M := ComplexEuclideanManifold n hn) F z ht]
    exact hmaps (radial_target_mem hw ht)
  have hT := targetParameter_smooth ctarget w0 delta hW
  have hT0 : targetParameter ctarget w0 0 = Phi 0 := by
    simpa only [targetParameter, add_zero] using hp0.symm
  obtain ⟨target, htarget, hlen⟩ := exists_radial_curve hs hT0 hT hL
    (fun q hq v => targetParameter_upper k ctarget w0 delta L hW hG q hq v) hz
  have hPhiSmooth := hPhi.1
  have hcurves : ∀ t ∈ Icc (0 : ℝ) 1,
      mappedCurve hPhiSmooth hn source.1 hmem t = target.1 t := by
    intro t ht
    rw [mappedCurve_on_interval hPhiSmooth hn source.1 hmem ht]
    change Phi (radialPath (M := ComplexEuclideanManifold n hn) F z t) = target.1 t
    rw [radialPath_eq (M := ComplexEuclideanManifold n hn) F z ht]
    change Phi (sigma (w0 + t • z)) = target.1 t
    rw [hright _ (radial_target_mem hw ht)]
    exact (htarget t ht).symm
  have hleneq := curveLength_eq_on_interval k
    (mappedCurve hPhiSmooth hn source.1 hmem) target.1 hcurves
  rw [mappedCurve_length_eq hPhiSmooth hn ks k heq source.1 hmem] at hleneq
  have H := (inducedDistance_le_curveLength ks source).trans (hleneq.trans_le hlen)
  have hpoint : F z = sigma w := by
    dsimp [F, z]
    congr 1
    abel
  change inducedDistance ks 0 (F z) ≤ L * ‖z‖ at H
  rw [hpoint] at H
  exact H

end Yau.Proofs.C03Aux.ShortLift
