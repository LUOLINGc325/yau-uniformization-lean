import Yau.Proofs.P07DistanceLeviProfile
import Yau.Proofs.P07SupportWeakTests

/-! The actual radial distance truncations satisfy the original weak
Levi upper bound, with one scale independent positive constant. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux

variable {n : ℕ}

theorem radialTruncation_weakLeviUpper (X : KahlerManifold n) (o : Pt X)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hmono : Monotone χ)
    (hone : ∀ s : ℝ, 4 ≤ s → χ s = 1)
    (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hbound : ∀ s : ℝ, |deriv χ s| ≤ A₁ ∧ |deriv (deriv χ) s| ≤ A₂) :
    ∃ A : ℝ, 0 < A ∧ ∀ L : ℝ, 0 < L →
      WeakLeviUpper X.metric.form
        (fun x => χ ((distFrom X.metric.form o x) ^ 2 / L ^ 2)) (A / L ^ 2) := by
  obtain ⟨A,hA,hSupports⟩ := radialTruncation_localUpperSupports X o χ hχ hmono hone
    A₁ A₂ hA₁ hA₂ hbound
  refine ⟨A,hA,?_⟩
  intro L hL
  apply P07Aux.SupportWeak.weakLeviUpper_of_localUpperSupports X.metric
    (hχ.continuous.comp (((continuous_distFrom X.metric o).pow 2).div_const (L^2))) (A/L^2)
  intro c z hz
  exact hSupports L hL c z hz

end Yau.NodeProofs.P07DistanceLevi
