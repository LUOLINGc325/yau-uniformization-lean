import Yau.Proofs.C07LiftUniqueness
import Yau.Proofs.C07InverseHolomorphic

/-! Genuine inverse branches and transitions agree on a connected manifold domain. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem manifold_inverse_branches_unique
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    {V : Set M.Carrier} (hV : IsPreconnected V) {o : M.Carrier} (ho : o ∈ V)
    {f g : M.Carrier → ComplexVector n} (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (hfball : ∀ x ∈ V, f x ∈ Metric.ball 0 r)
    (hgball : ∀ x ∈ V, g x ∈ Metric.ball 0 r)
    (hflift : ∀ x ∈ V, Φ (f x) = x) (hglift : ∀ x ∈ V, Φ (g x) = x)
    (hfzero : f o = 0) (hgzero : g o = 0) : EqOn f g V := by
  letI : PreconnectedSpace V := Subtype.preconnectedSpace hV
  have hfc : Continuous (fun x : V => f x) := continuousOn_iff_continuous_domRestrict.mp hf
  have hgc : Continuous (fun x : V => g x) := continuousOn_iff_continuous_domRestrict.mp hg
  have hcomp : Φ ∘ (fun x : V => f x) = Φ ∘ (fun x : V => g x) := by
    funext x
    exact (hflift x x.2).trans (hglift x x.2).symm
  have heq := chart_lifts_unique hΦ hfc hgc
    (fun x => hfball x x.2) (fun x => hgball x x.2) hcomp
    (⟨o, ho⟩ : V) (hfzero.trans hgzero.symm)
  exact fun x hx => congrFun heq ⟨x, hx⟩

theorem inverse_transition_coherence
    {Φ Ψ : ComplexVector n → M.Carrier} {F : ComplexVector n → ComplexVector n}
    {r R : ℝ} (hΨ : IsLocalBiholomorphism Ψ r)
    {V : Set M.Carrier} (hV : IsPreconnected V) {o : M.Carrier} (ho : o ∈ V)
    {f g : M.Carrier → ComplexVector n} (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (hF : ContinuousOn F (Metric.ball 0 R))
    (hfball : ∀ x ∈ V, f x ∈ Metric.ball 0 R)
    (hgball : ∀ x ∈ V, g x ∈ Metric.ball 0 r)
    (hFball : ∀ z ∈ Metric.ball 0 R, F z ∈ Metric.ball 0 r)
    (hflift : ∀ x ∈ V, Φ (f x) = x) (hglift : ∀ x ∈ V, Ψ (g x) = x)
    (htransition : ∀ z ∈ Metric.ball 0 R, Ψ (F z) = Φ z)
    (hfzero : f o = 0) (hgzero : g o = 0) (hFzero : F 0 = 0) :
    EqOn g (F ∘ f) V := by
  have hcomp : ContinuousOn (F ∘ f) V := hF.comp hf hfball
  apply manifold_inverse_branches_unique hΨ hV ho hg hcomp hgball
    (fun x hx => hFball _ (hfball x hx)) hglift
  · intro x hx
    exact (htransition _ (hfball x hx)).trans (hflift x hx)
  · exact hgzero
  · change F (f o) = 0
    rw [hfzero, hFzero]

theorem continuous_manifold_inverse_mdifferentiable
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    {V : Set M.Carrier} (hV : IsOpen V) {f : M.Carrier → ComplexVector n}
    (hf : ContinuousOn f V) (hball : ∀ x ∈ V, f x ∈ Metric.ball 0 r)
    (hlift : ∀ x ∈ V, Φ (f x) = x) :
    MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) f V := by
  intro x hx
  obtain ⟨e, hfx, hsource, heq⟩ :=
    local_homeomorph_of_localBiholomorphism hΦ (hball x hx)
  have htarget : x ∈ e.target := by
    have h := e.map_source hfx
    rwa [heq hfx, hlift x hx] at h
  have heinv : MDifferentiableAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) e.symm x :=
    (inverse_branch_mdifferentiable hΦ e hsource heq).mdifferentiableAt
      (e.open_target.mem_nhds htarget)
  have hnear : ∀ᶠ y in 𝓝 x, f y ∈ e.source :=
    (hf.continuousAt (hV.mem_nhds hx)).eventually (e.open_source.mem_nhds hfx)
  have hgerm : f =ᶠ[𝓝 x] e.symm := by
    filter_upwards [hnear, hV.mem_nhds hx] with y hfy hy
    calc
      f y = e.symm (e (f y)) := (e.left_inv hfy).symm
      _ = e.symm y := by rw [heq hfy, hlift y hy]
  exact (heinv.congr_of_eventuallyEq hgerm).mdifferentiableWithinAt

end Yau.Proofs.C07Aux
