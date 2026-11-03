import Yau.Proofs.F01CompactApproximationIdentity
import Yau.Proofs.F01OpenPotentialExtension
import Yau.Proofs.F01LogDetRatioSmooth

/-! On every fixed compact core the actual approximating potential and
its original closed-time equation become the ambient metric-potential
identity and ambient-background determinant equation, without error terms. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem compact_ambient_approximate_flow_identity (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {K : Set (Pt X)} (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
      let N := sublevelManifold X.manifold u hu.1 o L ho
      let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
      let S := sublevelOpens X.manifold u hu.1 o L
      let hS := sublevelComponent_isConnected ho
      K ⊆ sublevelComponent u o L ∧
      ∀ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ) (I : Set ℝ),
        (∀ x t, t ∈ I → gMat (h t) x = gMat α x - (t : ℂ) • ricci α x + levi (fun y => U y t) x) →
        (∀ x t, t ∈ I → HasDerivWithinAt (U x) (flowLogDetRatio α h x t) I t) →
        ∀ x : N.Carrier, x.val ∈ K → ∀ t : ℝ, t ∈ I →
          gMat (h t) x = gMat X.metric.form x.val - (t : ℂ) • ricci X.metric.form x.val +
            levi (fun y => openExtendedPotential X.manifold S hS U y t) x.val ∧
          HasDerivWithinAt (openExtendedPotential X.manifold S hS U x.val)
            (Real.log ((gMat (h t) x).det.re / (gMat X.metric.form x.val).det.re)) I t := by
  obtain ⟨L0, hL0, hcore⟩ := compact_approximation_identity X o u hu hK
  refine ⟨L0, hL0, ?_⟩
  intro L hL ho
  dsimp only
  obtain ⟨hsubset, hident⟩ := hcore L hL ho
  refine ⟨hsubset, ?_⟩
  intro h U I hpot hpde x hx t ht
  have hbackground := hident x hx
  constructor
  · rw [hpot x t ht, hbackground.2.1, hbackground.2.2,
      openExtendedPotential_levi X.manifold (sublevelOpens X.manifold u hu.1 o L)
        (sublevelComponent_isConnected ho) U x t]
    rfl
  · have hh := openExtendedPotential_time_equation X.manifold
      (sublevelOpens X.manifold u hu.1 o L) (sublevelComponent_isConnected ho)
      U _ hpde x ht
    unfold flowLogDetRatio at hh
    rw [hbackground.2.1] at hh
    exact hh

end Yau.NodeProofs.F01Aux
