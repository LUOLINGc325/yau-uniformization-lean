import Yau.Proofs.C01InitialBisectional
import Yau.Proofs.C01RicciInitialInterval
import Yau.Proofs.C01RicciFramePropagation
import Yau.LeafProofs.L23FieldMetricLinearODEInterval

/-! The entire original strict Ricci clause.  Its initial positivity
comes from the paper hypothesis, and its actual moving frame is constructed
by the independently checked linear ODE theorem on positive compact intervals. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_ricci_posDef
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (t : ℝ) (ht : 0 ≤ t) (x : Pt X) : (ricci (h t) x).PosDef := by
  have hzero := localizedFlow_initial_ricci_posDef hflow x
  by_cases ht0 : t = 0
  · simpa only [ht0] using hzero
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  obtain ⟨ε, hε, hinitial⟩ := localizedFlow_ricci_posDef_initial_interval hflow hjoint x hzero
  let a := min ε t / 2
  have hmin : 0 < min ε t := lt_min hε htpos
  have ha : 0 < a := half_pos hmin
  have hat : a < t := by dsimp only [a]; linarith [min_le_right ε t]
  have haε : a ≤ ε := by dsimp only [a]; linarith [min_le_left ε t]
  have hsegment : Set.Icc a t ⊆ Set.Ioi 0 := by
    intro s hs
    exact ha.trans_le hs.1
  obtain ⟨δ, hδ, W, hWa, _hW, hsol⟩ :=
    Yau.LeafProofs.L23Aux.exists_interval_fundamental_solution
      (movingFrameCoefficient h x) (Set.Ioi 0) isOpen_Ioi
      (localizedFlow_movingFrameCoefficient_contDiffOn hflow x) a t hat hsegment
  apply localizedFlow_ricci_posDef_of_movingFrame hflow hjoint x W a t ha hat.le hWa
  · intro s hs
    have hsI : s ∈ Set.Ioo (a - δ) (t + δ) := by
      constructor <;> linarith [hs.1, hs.2]
    exact (hsol s hsI).2
  · exact hinitial a ⟨ha.le, haε⟩

end Yau.NodeProofs.C01Aux
