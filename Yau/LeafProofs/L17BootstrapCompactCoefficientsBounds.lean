import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! Nonnegative ordinary bounds on one fixed compact parameter-coordinate-time box. -/

noncomputable section
open Set Metric

namespace Yau.LeafProofs.L17BootstrapCompactCoefficientsAux

variable {X F G H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]

theorem exists_nonneg_bound_three {K : Set X} (hK : IsCompact K)
    (f : X → F) (g : X → G) (h : X → H)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (hh : ContinuousOn h K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖f x‖ ≤ B ∧ ‖g x‖ ≤ B ∧ ‖h x‖ ≤ B := by
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hf
  obtain ⟨Z,hZ⟩ := hK.exists_bound_of_continuousOn hg
  obtain ⟨U,hU⟩ := hK.exists_bound_of_continuousOn hh
  let B := max 0 (max A (max Z U))
  have hAB : A ≤ B := (le_max_left A (max Z U)).trans (le_max_right _ _)
  have hZB : Z ≤ B := (le_max_left Z U).trans ((le_max_right A (max Z U)).trans (le_max_right _ _))
  have hUB : U ≤ B := (le_max_right Z U).trans ((le_max_right A (max Z U)).trans (le_max_right _ _))
  exact ⟨B,le_max_left _ _,fun x hx => ⟨(hA x hx).trans hAB,(hZ x hx).trans hZB,(hU x hx).trans hUB⟩⟩

/-- The compact set is fixed before the order is selected. Targets may vary with
the derivative order and need not be finite-dimensional. -/
theorem exists_order_budgets {K : Set X} (hK : IsCompact K)
    {F0 Fz Ft : ℕ → Type*}
    [∀ k, NormedAddCommGroup (F0 k)] [∀ k, NormedAddCommGroup (Fz k)]
    [∀ k, NormedAddCommGroup (Ft k)]
    (f0 : ∀ k, X → F0 k) (fz : ∀ k, X → Fz k) (ft : ∀ k, X → Ft k)
    (h0 : ∀ k, ContinuousOn (f0 k) K) (hz : ∀ k, ContinuousOn (fz k) K)
    (ht : ∀ k, ContinuousOn (ft k) K) :
    ∃ B : ℕ → ℝ, ∀ k, 0 ≤ B k ∧
      ∀ x ∈ K, ‖f0 k x‖ ≤ B k ∧ ‖fz k x‖ ≤ B k ∧ ‖ft k x‖ ≤ B k := by
  classical
  have hb : ∀ k, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K,
      ‖f0 k x‖ ≤ B ∧ ‖fz k x‖ ≤ B ∧ ‖ft k x‖ ≤ B :=
    fun k => exists_nonneg_bound_three hK (f0 k) (fz k) (ft k) (h0 k) (hz k) (ht k)
  exact ⟨fun k => Classical.choose (hb k),fun k => Classical.choose_spec (hb k)⟩

def compactMixedBox (Param E : Type*) [NormedAddCommGroup Param] [NormedAddCommGroup E]
    (R rho T : ℝ) : Set (Param × (E × ℝ)) :=
  closedBall (0 : Param) R ×ˢ (closedBall (0 : E) rho ×ˢ Icc (0 : ℝ) T)

theorem isCompact_compactMixedBox (Param E : Type*)
    [NormedAddCommGroup Param] [NormedAddCommGroup E] [ProperSpace Param] [ProperSpace E]
    (R rho T : ℝ) : IsCompact (compactMixedBox Param E R rho T) :=
  (isCompact_closedBall (0 : Param) R).prod
    ((isCompact_closedBall (0 : E) rho).prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)))

end Yau.LeafProofs.L17BootstrapCompactCoefficientsAux
