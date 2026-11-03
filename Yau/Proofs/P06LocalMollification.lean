import Yau.Proofs.P06WeakLeviConvolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03 Yau.LeafProofs.L18Aux

theorem exists_compact_model_L1_extension {n : ℕ} {O K : Set (ComplexVector n)}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ComplexVector n → ℝ) (hu : ContinuousOn u O) :
    ∃ F : ComplexVector n → ℝ, Continuous F ∧ HasCompactSupport F ∧
      Integrable F volume ∧ Set.EqOn F u K := by
  obtain ⟨χ, hχ, hcχ, hsχ, _, hχone⟩ := exists_model_chart_cutoff hO hK hKO
  let F : ComplexVector n → ℝ := fun z => χ z * u z
  have hFC : Continuous F := continuous_mul_of_continuousAt_tsupport hχ.continuous
    (fun z hz => hu.continuousAt (hO.mem_nhds (hsχ hz)))
  have hcF : HasCompactSupport F := hcχ.mul_right
  refine ⟨F, hFC, hcF, hFC.integrable_of_hasCompactSupport hcF, ?_⟩
  intro z hz
  change χ z * u z = u z
  rw [(hχone z hz).1, one_mul]

/-- Local normalized mollification is genuinely constructed from a rough
continuous datum. The original weak Levi inequality controls its actual
smooth Hessian, and the approximation is uniform on the given compact. -/
theorem weakLeviUpper_local_mollification {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (hf : Continuous f) (C : ℝ)
    (hw : WeakLeviUpper g.form f C) (x : M.Carrier) (K : Set (ComplexVector n))
    (hK : IsCompact K) (hKO : K ⊆ chartTarget x) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : ContDiffBump (0 : ComplexVector n), φ.rOut < r →
      ∃ U : ComplexVector n → ℝ, ContDiff ℝ ∞ U ∧
        (∀ z ∈ K, |U z - inChart x f z| ≤ ε) ∧
        ∀ z ∈ K, ∀ v : ComplexVector n,
          leviDirection (leviC U z) v ≤
            C * ∫ a, φ.normed volume (z - a) * leviDirection (hMat g.form x a) v := by
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hu : ContinuousOn (inChart x f) (chartTarget x) :=
    hf.comp_continuousOn (continuousOn_extChartAt_symm (I := ComplexModel n) x)
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  let D : Set (ComplexVector n) := Metric.cthickening δ K
  have hD : IsCompact D := hK.cthickening
  obtain ⟨F, hFC, hcF, hFI, hFeq⟩ := exists_compact_model_L1_extension hO hD hδO (inChart x f) hu
  have hUF := hD.uniformContinuousOn_of_continuous hFC.continuousOn
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp hUF ε hε
  refine ⟨min δ d, lt_min hδ hd, ?_⟩
  intro φ hφ
  have hφδ : φ.rOut < δ := hφ.trans_le (min_le_left δ d)
  have hφd : φ.rOut < d := hφ.trans_le (min_le_right δ d)
  let U : ComplexVector n → ℝ := φ.normed volume ⋆[lsmul ℝ ℝ, volume] F
  have hsmooth : ContDiff ℝ ∞ U :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed hFI.locallyIntegrable
  have hKD : K ⊆ D := Metric.self_subset_cthickening K
  have hsupport (z : ComplexVector n) (hz : z ∈ K) :
      {a | z - a ∈ tsupport (φ.normed volume)} ⊆ D := by
    intro a ha
    rw [φ.tsupport_normed_eq] at ha
    have hnorm : ‖z - a‖ ≤ φ.rOut := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq] using ha
    apply Metric.closedBall_subset_cthickening hz δ
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [norm_sub_rev]
    exact hnorm.trans hφδ.le
  refine ⟨U, hsmooth, ?_, ?_⟩
  · intro z hz
    have hbound : ∀ a ∈ Metric.ball z φ.rOut, dist (F a) (F z) ≤ ε := by
      intro a ha
      have hp : a ∈ D := Metric.closedBall_subset_cthickening hz δ
        (Metric.ball_subset_closedBall (Metric.ball_subset_ball hφδ.le ha))
      exact (hdist a hp z (hKD hz) ((Metric.mem_ball.mp ha).trans hφd)).le
    have hb := φ.dist_normed_convolution_le (μ := volume) hFC.aestronglyMeasurable hbound
    rw [hFeq (hKD hz)] at hb
    simpa only [U, Real.dist_eq] using hb
  · intro z hz v
    exact weakLeviUpper_convolution_direction g f C hw x (φ.normed volume) φ.contDiff_normed
      φ.hasCompactSupport_normed φ.nonneg_normed F hFI z
      (fun a ha => hFeq (hsupport z hz ha)) ((hsupport z hz).trans hδO) v

end Yau.NodeProofs.P06Aux
