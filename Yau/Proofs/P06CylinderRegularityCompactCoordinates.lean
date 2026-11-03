import Yau.Proofs.P06CylinderRegularityFormEstimate

/-! Smooth compact coordinate extensions on a prescribed positive chart
cylinder, chosen only after the uniform estimate constants are fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03 Yau.LeafProofs.L16Aux

theorem exists_compact_hodge_coordinates {n k : ℕ} {M : ComplexManifold n}
    (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Set.Ioi 0))
    (x : M.Carrier) {α : Type} [Fintype α] (b : Basis α ℝ (HodgeJets.Fiber n k))
    {Q : Set (Point n)} (hcQ : IsCompact (closure Q))
    (hClosure : closure Q ⊆ chartTarget x ×ˢ Set.Ioi 0) :
    ∃ W : Point n → α → ℝ, (∀ r, ContDiff ℝ ∞ (fun p => W p r)) ∧
      (∀ r, HasCompactSupport (fun p => W p r)) ∧
      ∀ p ∈ Q, ∀ r, (fun s => W s r) =ᶠ[𝓝 p]
        (fun s => hodgeRegularityCoord b (U s.2) x s.1 r) := by
  have hO : IsOpen (chartTarget x ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  obtain ⟨ζ,hζ,hζNear⟩ := exists_test_eq_one_near_compact hO hcQ hClosure
  let W : Point n → α → ℝ := fun p r => ζ p * hodgeRegularityCoord b (U p.2) x p.1 r
  have hW (r : α) := cutoff_contDiff hO hζ.1 hζ.2.1 hζ.2.2
    (hodgeCoordinate_joint_contDiffOn U hU x b r)
  exact ⟨W,fun r => (hW r).1,fun r => (hW r).2,
    fun p hp r => cutoff_eq_germ (hζNear p (subset_closure hp))⟩

theorem weighted_hodge_coordinates_germ {n k : ℕ} {M : ComplexManifold n}
    (U : ℝ → RealForm M k) (x : M.Carrier) {α : Type} [Fintype α]
    (b : Basis α ℝ (HodgeJets.Fiber n k)) (W : Point n → α → ℝ) (p : Point n)
    (hg : ∀ r, (fun s => W s r) =ᶠ[𝓝 p]
      (fun s => hodgeRegularityCoord b (U s.2) x s.1 r)) (I : Fin k → RIdx n) :
    (fun p => ∑ r, (b r) (fun j => realVec (I j)) * W p r) =ᶠ[𝓝 p]
      (fun p : Point n => formComponents (U p.2) x p.1 I) := by
  have hAll := (Filter.eventually_all.mpr hg)
  filter_upwards [hAll] with s hs
  simp_rw [hs]
  exact form_component_basis_expansion b (U s.2) x s.1 I

end Yau.NodeProofs.P06Aux.CylinderReg
