import Yau.Blueprint.Alignment

/-! One common matrix subsequence for every index of an infinite regular tail. -/

open scoped Topology Matrix Matrix.Norms.Elementwise
open Filter Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem norm_entry_le_matOpNorm (A : Herm n) (i j : Fin n) : ‖A i j‖ ≤ matOpNorm A := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  have hcoord : (T (stdVec j)) i = A i j := by
    simp [T, stdVec, EuclideanSpace.single, Matrix.mulVec_single]
  have hnorm : ‖stdVec j‖ = 1 := by simp [stdVec, EuclideanSpace.single]
  calc
    ‖A i j‖ = ‖(T (stdVec j)) i‖ := congrArg norm hcoord.symm
    _ ≤ ‖T (stdVec j)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖stdVec j‖ := T.le_opNorm _
    _ = matOpNorm A := by rw [hnorm, mul_one]; rfl

theorem common_matrix_subsequence (L : ℕ → ℕ → Herm n) (B : ℕ → ℝ)
    (hbound : ∀ H k, matOpNorm (L H k) ≤ B k) :
    ∃ (A : ℕ → Herm n) (subseq : ℕ → ℕ), StrictMono subseq ∧
      Tendsto (fun H => L (subseq H)) atTop (𝓝 A) ∧
      ∀ k i j, Tendsto (fun H => L (subseq H) k i j) atTop (𝓝 (A k i j)) := by
  haveI : FirstCountableTopology (Herm n) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  let balls : ℕ → Set (Herm n) := fun k => Metric.closedBall 0 (max 1 (B k))
  have hcompact : IsCompact (Set.pi univ balls) :=
    isCompact_univ_pi fun k => isCompact_closedBall _ _
  have hmem : ∀ H, L H ∈ Set.pi univ balls := by
    intro H k _
    dsimp only [balls]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hnonneg : (0 : ℝ) ≤ max 1 (B k) := le_trans zero_le_one (le_max_left _ _)
    apply (pi_norm_le_iff_of_nonneg hnonneg).2
    intro i
    apply (pi_norm_le_iff_of_nonneg hnonneg).2
    intro j
    exact (norm_entry_le_matOpNorm (L H k) i j).trans ((hbound H k).trans (le_max_right _ _))
  obtain ⟨A, _, subseq, hmono, hlim⟩ := hcompact.tendsto_subseq hmem
  refine ⟨A, subseq, hmono, hlim, ?_⟩
  intro k i j
  exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim k) i) j

end Yau.Blueprint.Alignment.Y03Proof
