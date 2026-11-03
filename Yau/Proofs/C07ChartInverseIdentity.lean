import Yau.Proofs.C07LiftUniqueness

/-! The constructed inverse and the identity are the same actual chart lift. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem inverse_comp_chart_eq_on_closedBall
    {Φ : ComplexVector n → M.Carrier} {r ε : ℝ}
    (hΦ : IsLocalBiholomorphism Φ r) (hε : 0 ≤ ε) (hεr : ε < r)
    {Ω : Set M.Carrier} {f : M.Carrier → ComplexVector n}
    (hf : ContinuousOn f Ω) (hp : ∀ x ∈ Ω, f x ∈ Metric.ball 0 r ∧ Φ (f x) = x)
    (hzero : f (Φ 0) = 0) (hmaps : MapsTo Φ (Metric.closedBall 0 ε) Ω) :
    EqOn (f ∘ Φ) id (Metric.closedBall (0 : ComplexVector n) ε) := by
  let A := Metric.closedBall (0 : ComplexVector n) ε
  letI : PreconnectedSpace A :=
    Subtype.preconnectedSpace (convex_closedBall (0 : ComplexVector n) ε).isPreconnected
  have hsub : A ⊆ Metric.ball (0 : ComplexVector n) r := Metric.closedBall_subset_ball hεr
  have hc : ContinuousOn Φ A := hΦ.1.continuousOn.mono hsub
  have hfc : Continuous (fun z : A => f (Φ z)) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.comp hc hmaps)
  have hcomp : Φ ∘ (fun z : A => f (Φ z)) = Φ ∘ (fun z : A => (z : ComplexVector n)) := by
    funext z
    exact (hp (Φ z) (hmaps z.2)).2
  have hmem : (0 : ComplexVector n) ∈ A := Metric.mem_closedBall_self hε
  have heq := chart_lifts_unique hΦ hfc continuous_subtype_val
    (fun z => (hp (Φ z) (hmaps z.2)).1) (fun z => hsub z.2) hcomp
    (⟨0, hmem⟩ : A) hzero
  exact fun z hz => congrFun heq ⟨z, hz⟩

end Yau.Proofs.C07Aux
