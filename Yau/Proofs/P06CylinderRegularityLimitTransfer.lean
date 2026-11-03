import Yau.Proofs.P06LocalCauchyLimitForms

/-! Two families with vanishing mixed joint-jet differences have the same
actual local smooth limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem jointJetLimit_of_mixed_cauchy {n k : ℕ} {M : ComplexManifold n}
    (Us Vs : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hUs : ∀ j, 1 ≤ j → SmoothFormTime (Us j) (Set.Ioi 0))
    (hVs : ∀ j, 1 ≤ j → SmoothFormTime (Vs j) (Set.Ioi 0))
    (hU : SmoothFormTime U (Set.Ioi 0)) (hLimit : LocalCauchyLimit.JointJetLimit Us U)
    (hc : ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
      ∀ eps T, 0 < eps → eps < T → ∀ (m : ℕ) (I : Fin k → RIdx n) η, 0 < η →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ j l, N ≤ j → N ≤ l → ∀ z ∈ K, ∀ t ∈ Set.Icc eps T,
        ‖iteratedFDeriv ℝ m (fun p : Point n =>
          formComponents (Us j p.2) x p.1 I-formComponents (Vs l p.2) x p.1 I) (z,t)‖ < η) :
    LocalCauchyLimit.JointJetLimit Vs U := by
  intro x K hK hKx eps T heps heT m I η hη
  obtain ⟨N,hNpos,hN⟩ := hc x K hK hKx eps T heps heT m I (η/2) (half_pos hη)
  obtain ⟨L,hL⟩ := hLimit x K hK hKx eps T heps heT m I (η/2) (half_pos hη)
  let j := max N L
  have hjN : N ≤ j := le_max_left _ _
  have hjL : L ≤ j := le_max_right _ _
  have hj1 : 1 ≤ j := hNpos.trans hjN
  refine ⟨N,?_⟩
  intro l hl z hz t ht
  have hl1 : 1 ≤ l := hNpos.trans hl
  have hp : (z,t) ∈ chartTarget x ×ˢ Set.Ioi (0 : ℝ) :=
    ⟨hKx hz,heps.trans_le ht.1⟩
  have hOpen : IsOpen (chartTarget x ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  have hA := ((hUs j hj1 x I).contDiffAt (hOpen.mem_nhds hp)).of_le (show (m : ℕ∞ω) ≤ ∞ by simp)
  have hB := ((hVs l hl1 x I).contDiffAt (hOpen.mem_nhds hp)).of_le (show (m : ℕ∞ω) ≤ ∞ by simp)
  have hC := ((hU x I).contDiffAt (hOpen.mem_nhds hp)).of_le (show (m : ℕ∞ω) ≤ ∞ by simp)
  have h1 := hN j l hjN hl z hz t ht
  have h2 := hL j hjL z hz t ht
  change ‖iteratedFDeriv ℝ m
    ((fun p : Point n => formComponents (Us j p.2) x p.1 I)-
      (fun p : Point n => formComponents (Vs l p.2) x p.1 I)) (z,t)‖ < η/2 at h1
  change ‖iteratedFDeriv ℝ m
    ((fun p : Point n => formComponents (Us j p.2) x p.1 I)-
      (fun p : Point n => formComponents (U p.2) x p.1 I)) (z,t)‖ < η/2 at h2
  change ‖iteratedFDeriv ℝ m
    ((fun p : Point n => formComponents (Vs l p.2) x p.1 I)-
      (fun p : Point n => formComponents (U p.2) x p.1 I)) (z,t)‖ < η
  rw [iteratedFDeriv_sub_apply hA hB] at h1
  rw [iteratedFDeriv_sub_apply hA hC] at h2
  rw [iteratedFDeriv_sub_apply hB hC]
  let A := iteratedFDeriv ℝ m (fun p : Point n => formComponents (Us j p.2) x p.1 I) (z,t)
  let B := iteratedFDeriv ℝ m (fun p : Point n => formComponents (Vs l p.2) x p.1 I) (z,t)
  let C := iteratedFDeriv ℝ m (fun p : Point n => formComponents (U p.2) x p.1 I) (z,t)
  change ‖A-B‖ < η/2 at h1
  change ‖A-C‖ < η/2 at h2
  change ‖B-C‖ < η
  calc
    ‖B-C‖ = ‖(A-C)-(A-B)‖ := by congr 1; abel
    _ ≤ ‖A-C‖+‖A-B‖ := norm_sub_le _ _
    _ < η := by linarith

end Yau.NodeProofs.P06Aux.CylinderReg
