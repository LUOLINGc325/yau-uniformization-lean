import Yau.LeafProofs.L16EnergyLimit

/-! Two genuine nonnegative compact test cutoffs and uniform derivative bounds. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem exists_nonnegative_test_eq_one_near_compact {D K : Set (Point d)}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ η : Point d → ℝ, Test D η ∧ (∀ p, η p ∈ Icc (0 : ℝ) 1) ∧
      ∀ p ∈ K, η =ᶠ[𝓝 p] (fun _ => 1) := by
  obtain ⟨V,hV,hKV,hVD,hVc⟩ := exists_open_between_and_isCompact_closure hK hD hKD
  obtain ⟨W,hW,hVW,hWD,hWc⟩ := exists_open_between_and_isCompact_closure hVc hD hVD
  obtain ⟨η,hη,hRange,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW (isClosed_closure : IsClosed (closure V)) hVW
  have hcη : HasCompactSupport η := by
    change IsCompact (tsupport η)
    simpa only [tsupport,hSupport] using hWc
  have hηD : tsupport η ⊆ D := by simpa only [tsupport,hSupport] using hWD
  refine ⟨η,⟨hη,hcη,hηD⟩,fun p => hRange (mem_range_self p),?_⟩
  intro p hp
  filter_upwards [hV.mem_nhds (hKV hp)] with q hq
  exact (hOne q).mp (subset_closure hq)

theorem test_joint_directional_derivatives_bounded {D : Set (Point d)}
    (η : Point d → ℝ) (hη : Test D η) :
    ∃ M : ℝ, 0 < M ∧ (∀ p, |fderiv ℝ η p (0,1)| ≤ M) ∧
      ∀ p, ∀ i : RIdx d, |fderiv ℝ η p (realVec i,0)| ≤ M := by
  classical
  let E : Option (RIdx d) → Point d
    | none => (0,1)
    | some i => (realVec i,0)
  have hEach : ∀ i : Option (RIdx d), ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |fderiv ℝ η p (E i)| ≤ C := by
    intro i
    have hT := test_directionalDerivative hη (E i)
    obtain ⟨C,hC⟩ := hT.1.continuous.bounded_above_of_compact_support hT.2.1
    refine ⟨max 0 C,le_max_left _ _,?_⟩
    intro p
    exact (show |fderiv ℝ η p (E i)| ≤ C by simpa only [Real.norm_eq_abs] using hC p).trans (le_max_right _ _)
  choose C hC0 hC using hEach
  let M : ℝ := 1+∑ i,C i
  have hM : 0 < M := by dsimp [M];exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => hC0 i))
  have hBound : ∀ i p, |fderiv ℝ η p (E i)| ≤ M := by
    intro i p
    have hi : C i ≤ ∑ j,C j := Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)
    exact (hC i p).trans (hi.trans (by dsimp [M];linarith))
  exact ⟨M,hM,hBound none,fun p i => hBound (some i) p⟩

end Yau.Proofs.F03Aux
