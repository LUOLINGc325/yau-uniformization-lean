import Yau.Proofs.C07InverseHolomorphic

/-! A continuous lift of one actual holomorphic chart through another is nonsingular holomorphic. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Filter

variable {n : ℕ} {M : ComplexManifold n}

theorem continuous_transition_holomorphic
    {Φ Ψ : ComplexVector n → M.Carrier} {F : ComplexVector n → ComplexVector n}
    {r R q : ℝ} (hΦ : IsLocalBiholomorphism Φ r) (hΨ : IsLocalBiholomorphism Ψ R)
    (hqr : q ≤ r) (hF : ContinuousOn F (Metric.ball 0 q))
    (hball : ∀ z ∈ Metric.ball 0 q, F z ∈ Metric.ball 0 R)
    (hlift : ∀ z ∈ Metric.ball 0 q, Ψ (F z) = Φ z) :
    DifferentiableOn ℂ F (Metric.ball 0 q) ∧
      ∀ z ∈ Metric.ball 0 q, Function.Bijective (fderiv ℂ F z) := by
  have hΦq : IsLocalBiholomorphism Φ q :=
    ⟨hΦ.1.mono (Metric.ball_subset_ball hqr),
      fun z hz => hΦ.2 z (Metric.ball_subset_ball hqr hz)⟩
  have hFd (z : ComplexVector n) (hz : z ∈ Metric.ball 0 q) : DifferentiableAt ℂ F z := by
    obtain ⟨e, hFe, hsource, heq⟩ :=
      local_homeomorph_of_localBiholomorphism hΨ (hball z hz)
    have htarget : Φ z ∈ e.target := by
      have h := e.map_source hFe
      rwa [heq hFe, hlift z hz] at h
    have heinv : MDifferentiableAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) e.symm (Φ z) :=
      (inverse_branch_mdifferentiable hΨ e hsource heq).mdifferentiableAt
        (e.open_target.mem_nhds htarget)
    have hΦd := (hΦq.1.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp)
    have hcomp : DifferentiableAt ℂ (fun w => e.symm (Φ w)) z :=
      (heinv.comp z hΦd).differentiableAt
    have hnear : ∀ᶠ w in 𝓝 z, F w ∈ e.source :=
      (hF.continuousAt (Metric.isOpen_ball.mem_nhds hz)).eventually (e.open_source.mem_nhds hFe)
    have hgerm : F =ᶠ[𝓝 z] (fun w => e.symm (Φ w)) := by
      filter_upwards [hnear, Metric.isOpen_ball.mem_nhds hz] with w hwe hw
      calc
        F w = e.symm (e (F w)) := (e.left_inv hwe).symm
        _ = e.symm (Φ w) := by rw [heq hwe, hlift w hw]
    exact hcomp.congr_of_eventuallyEq hgerm
  refine ⟨fun z hz => (hFd z hz).differentiableWithinAt, ?_⟩
  intro z hz
  let G : ComplexVector n → ComplexVector n := fun w => chartPt (Ψ (F z)) (Ψ w)
  let H : ComplexVector n → ComplexVector n := fun w => chartPt (Φ z) (Φ w)
  obtain ⟨hG, hGbij⟩ := coordinate_chart_invertible hΨ (hball z hz)
  obtain ⟨hH, hHbij⟩ := coordinate_chart_invertible hΦq hz
  change ContDiffAt ℂ ∞ G (F z) at hG
  change Function.Bijective (fderiv ℂ G (F z)) at hGbij
  change ContDiffAt ℂ ∞ H z at hH
  change Function.Bijective (fderiv ℂ H z) at hHbij
  have hgerm : (fun w => G (F w)) =ᶠ[𝓝 z] H := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    change chartPt (Ψ (F z)) (Ψ (F w)) = chartPt (Φ z) (Φ w)
    rw [hlift z hz, hlift w hw]
  have hD := ((hG.differentiableAt (by simp)).hasFDerivAt.comp z
    (hFd z hz).hasFDerivAt).congr_of_eventuallyEq hgerm.symm
  have hchain : (fderiv ℂ G (F z)).comp (fderiv ℂ F z) = fderiv ℂ H z := hD.fderiv.symm
  have hbij : Function.Bijective ((fderiv ℂ G (F z)).comp (fderiv ℂ F z)) := by
    rw [hchain]
    exact hHbij
  exact (hGbij.of_comp_iff' (fderiv ℂ F z)).mp hbij

end Yau.Proofs.C07Aux
