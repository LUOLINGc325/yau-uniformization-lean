import Yau.Proofs.C07LocalInversion

/-! The same three actual transition germs compose, using only local injectivity at the center. -/

open scoped Manifold Topology
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem transition_composition_germ
    {Φ Ψ Ω : ComplexVector n → M.Carrier} {F G H : ComplexVector n → ComplexVector n}
    {r : ℝ} (hr : 0 < r) (hΩ : IsLocalBiholomorphism Ω r)
    (hF : ContinuousAt F 0) (hG : ContinuousAt G 0) (hH : ContinuousAt H 0)
    (hF₀ : F 0 = 0) (hG₀ : G 0 = 0) (hH₀ : H 0 = 0)
    (hΦΨ : ∀ᶠ z in 𝓝 0, Ψ (F z) = Φ z)
    (hΨΩ : ∀ᶠ z in 𝓝 0, Ω (G z) = Ψ z)
    (hΦΩ : ∀ᶠ z in 𝓝 0, Ω (H z) = Φ z) :
    ∀ᶠ z in 𝓝 0, G (F z) = H z := by
  obtain ⟨e, he₀, _, heq⟩ :=
    local_homeomorph_of_localBiholomorphism hΩ (Metric.mem_ball_self hr)
  have hFt : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hF₀] using hF.tendsto
  have hGF : ContinuousAt (fun z => G (F z)) 0 :=
    (by simpa only [hF₀] using hG : ContinuousAt G (F 0)).comp hF
  have hGF₀ : G (F 0) = 0 := by rw [hF₀, hG₀]
  have hn : ∀ᶠ y in 𝓝 (0 : ComplexVector n), y ∈ e.source := by
    change e.source ∈ 𝓝 (0 : ComplexVector n)
    exact e.open_source.mem_nhds he₀
  have hsrcGF : ∀ᶠ z in 𝓝 0, G (F z) ∈ e.source :=
    hGF.eventually (by simpa only [hGF₀] using hn)
  have hsrcH : ∀ᶠ z in 𝓝 0, H z ∈ e.source :=
    hH.eventually (by simpa only [hH₀] using hn)
  filter_upwards [hsrcGF, hsrcH, hΦΨ, hFt.eventually hΨΩ, hΦΩ] with z hzGF hzH hzF hzG hzH'
  apply e.injOn hzGF hzH
  rw [heq hzGF, heq hzH, hzG, hzF, hzH']

end Yau.Proofs.C07Aux
