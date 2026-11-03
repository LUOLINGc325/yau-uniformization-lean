import Yau.Proofs.F03CaloricTestSpace

/-! Fixed compact coefficient bounds chosen before every weak solution. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem compact_finite_continuous_family_bound {ι : Type*} [Fintype ι]
    (K : Set (Point d)) (hK : IsCompact K) (f : ι → Point d → ℝ)
    (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C : ℝ, 0 < C ∧ ∀ i p, p ∈ K → |f i p| ≤ C := by
  classical
  have hEach : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, |f i p| ≤ C := by
    intro i
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hf i)
    refine ⟨max 0 C,le_max_left _ _,?_⟩
    intro p hp
    exact (show |f i p| ≤ C by simpa only [Real.norm_eq_abs] using hC p hp).trans (le_max_right _ _)
  choose C hC0 hC using hEach
  let A : ℝ := 1+∑ i,C i
  have hA : 0 < A := by dsimp [A];exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => hC0 i))
  refine ⟨A,hA,?_⟩
  intro i p hp
  have hi : C i ≤ ∑ j,C j := Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)
  exact (hC i p hp).trans (hi.trans (by dsimp [A];linarith))

theorem caloric_coefficients_compact_bounds (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (K : Set (Point d)) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ (∀ p ∈ K, ∀ i j, |a p i j| ≤ A) ∧
      ∀ p ∈ K, ∀ i, |energyDrift a b p i| ≤ B := by
  have hAcont : ∀ ij : RIdx d × RIdx d, ContinuousOn (fun p => a p ij.1 ij.2) K := by
    intro ij
    exact (((matrixEntryCLM ij.1 ij.2).contDiff.comp_contDiffOn hAB.1).continuousOn).mono hKD
  obtain ⟨A,hA,hAb⟩ := compact_finite_continuous_family_bound K hK
    (fun ij : RIdx d × RIdx d => fun p => a p ij.1 ij.2) hAcont
  obtain ⟨B,hB,hBb⟩ := compact_finite_continuous_family_bound K hK
    (fun i p => energyDrift a b p i) (fun i => (energyDrift_smooth hD hAB i).continuousOn.mono hKD)
  exact ⟨A,B,hA,hB,fun p hp i j => hAb (i,j) p hp,fun p hp i => hBb i p hp⟩

end Yau.Proofs.F03Aux
