import Yau.Blueprint.Alignment

/-! The germ transition equation gives the actual shared chart differential. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {M : ComplexManifold n}

theorem transition_center_mfderiv {Φ Ψ : ComplexVector n → M.Carrier}
    {F : ComplexVector n → ComplexVector n} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hΨ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Ψ (Metric.ball 0 R))
    (hF : DifferentiableOn ℂ F (Metric.ball 0 r)) (hFzero : F 0 = 0)
    (hgerm : ∀ᶠ z in 𝓝 0, Ψ (F z) = Φ z) :
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Ψ 0).comp (centerDeriv F) =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ 0 := by
  have hΨd : MDifferentiableAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) Ψ 0 :=
    (hΨ.contMDiffAt (Metric.ball_mem_nhds _ hR)).mdifferentiableAt (by norm_num)
  have hFd : DifferentiableAt ℂ F 0 := hF.differentiableAt (Metric.ball_mem_nhds _ hr)
  have hFmf : mfderiv 𝓘(ℂ, ComplexVector n) 𝓘(ℂ, ComplexVector n) F 0 = centerDeriv F :=
    hFd.hasFDerivAt.hasMFDerivAt.mfderiv
  have hfun : (fun z => Ψ (F z)) =ᶠ[𝓝 0] Φ := hgerm
  have heq : mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) (fun z => Ψ (F z)) 0 =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ 0 := hfun.mfderiv_eq
  have hchain := mfderiv_comp (I := 𝓘(ℂ, ComplexVector n))
    (I' := 𝓘(ℂ, ComplexVector n)) (I'' := ComplexModel n) 0
    (by simpa only [hFzero] using hΨd) hFd.mdifferentiableAt
  change mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) (fun z => Ψ (F z)) 0 = _ at hchain
  rw [heq, hFzero, hFmf] at hchain
  exact hchain.symm

theorem shrinkingCharts_center_chain {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {t t' : ℝ} (ht : t₀ ≤ t) (htt' : t ≤ t') :
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) (Φ t') 0).comp (centerDeriv (F t t')) =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) (Φ t) 0 := by
  have htrans := hCharts.2.2.2.2.2.1 t t' ht htt'
  exact transition_center_mfderiv hCharts.1 (hCharts.1.trans hCharts.2.1)
    (hCharts.2.2.2.2.1 t' (ht.trans htt')).1.1 htrans.1 htrans.2.2.1 htrans.2.2.2.1

end Yau.Blueprint.Alignment.Y03Proof
