import Yau.Proofs.E03GlobalGap

/-! The actual smooth rho gives exactly the compact absolute bound in ScalarComparison. -/

noncomputable section
open scoped Manifold Topology ContDiff
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem scalarGap_compact_bound (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (T : ℝ) (hT : 0 < T) (S : ℝ) (hST : S < T)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ y ∈ K, ∀ t ∈ Icc 0 S, |scalarGap X h T y t| ≤ C := by
  have hr : SmoothSpaceTime ρ (Icc 0 S) := fun c =>
    (hloc.2.2.2.1 c).mono (fun p hp => ⟨hp.1, hp.2.1⟩)
  have hc : ContinuousOn (fun p : Pt X × ℝ => ρ p.1 p.2) (univ ×ˢ Icc 0 S) :=
    Yau.F04Proof.smoothSpaceTime_continuousOn hr
  have hp : IsCompact (K ×ˢ Icc 0 S) := hK.prod isCompact_Icc
  have hi : IsCompact ((fun p : Pt X × ℝ => ρ p.1 p.2) '' (K ×ˢ Icc 0 S)) :=
    hp.image_of_continuousOn (hc.mono (fun p hp => ⟨Set.mem_univ _, hp.2⟩))
  obtain ⟨C, hC⟩ := hi.bddAbove
  refine ⟨C, ?_⟩
  intro y hy t ht
  have hb := scalarGap_bounds o h U P ρ hloc hopt T hT S hST y t ht
  rw [abs_of_nonneg hb.1]
  exact hb.2.trans (hC ⟨(y, t), ⟨hy, ht⟩, rfl⟩)

end Yau.NodeProofs.E03Aux
