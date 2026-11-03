import Yau.Proofs.C04InverseJetsPartitions
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Isolate the genuine linear leading term in Faà di Bruno's formula. -/

noncomputable section
open Finset

namespace Yau.Proofs.C04Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverseJet_coarse_term {m : ℕ} (hm : 0 < m)
    (q p : FormalMultilinearSeries ℝ E E) (A : E →L[ℝ] E)
    (hq : ∀ v : Fin 1 → E, q 1 v = A (v 0)) :
    q.compAlongOrderedFinpartition p (inverseJetCoarse m hm) =
      A.compContinuousMultilinearMap (p m) := by
  ext v
  change q 1 (fun _ => p m (v ∘ id)) = A (p m v)
  rw [hq]
  rfl

theorem inverseJet_norm_le_linear_image {m : ℕ} (A : E →L[ℝ] E)
    (hA : A.IsInvertible) (P : E [×m]→L[ℝ] E) :
    ‖P‖ ≤ ‖A.inverse‖ * ‖A.compContinuousMultilinearMap P‖ := by
  have heq : A.inverse.compContinuousMultilinearMap (A.compContinuousMultilinearMap P) = P := by
    ext v
    exact hA.inverse_apply_self (P v)
  calc
    ‖P‖ = ‖A.inverse.compContinuousMultilinearMap (A.compContinuousMultilinearMap P)‖ := congrArg norm heq.symm
    _ ≤ ‖A.inverse‖ * ‖A.compContinuousMultilinearMap P‖ :=
      A.inverse.norm_compContinuousMultilinearMap_le _

theorem inverseJet_remainder_bound {m : ℕ} (hm : 0 < m)
    (q p : FormalMultilinearSeries ℝ E E) (B P : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hP : ∀ j, 0 ≤ P j)
    (hq : ∀ j, j ≤ m → ‖q j‖ ≤ B j)
    (hp : ∀ j, j < m → ‖p j‖ ≤ P j) :
    ‖∑ c ∈ (Finset.univ.erase (inverseJetCoarse m hm)), q.compAlongOrderedFinpartition p c‖ ≤
      ∑ c ∈ (Finset.univ.erase (inverseJetCoarse m hm)),
        B c.length * ∏ i : Fin c.length, P (c.partSize i) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c hc
  have hne : c ≠ inverseJetCoarse m hm := (Finset.mem_erase.mp hc).1
  calc
    ‖q.compAlongOrderedFinpartition p c‖ ≤ ‖q c.length‖ * ∏ i : Fin c.length, ‖p (c.partSize i)‖ :=
      c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ B c.length * ∏ i : Fin c.length, P (c.partSize i) := by
      gcongr
      · exact hB _
      · exact hq _ c.length_le
      · exact hp _ (inverseJet_partition_part_lt hm c hne _)

theorem inverseJet_coefficient_bound {m : ℕ} (hm : 0 < m)
    (q p : FormalMultilinearSeries ℝ E E) (B P : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (hP : ∀ j, 0 ≤ P j)
    (hq : ∀ j, j ≤ m → ‖q j‖ ≤ B j)
    (hp : ∀ j, j < m → ‖p j‖ ≤ P j)
    (A : E →L[ℝ] E) (hA : A.IsInvertible)
    (hlinear : ∀ v : Fin 1 → E, q 1 v = A (v 0))
    {L : ℝ} (hL : 0 ≤ L) (hAnorm : ‖A.inverse‖ ≤ L)
    (hidentity : ‖q.taylorComp p m‖ ≤ 1) :
    ‖p m‖ ≤ L * (1 + ∑ c ∈ (Finset.univ.erase (inverseJetCoarse m hm)),
      B c.length * ∏ i : Fin c.length, P (c.partSize i)) := by
  let c₀ := inverseJetCoarse m hm
  let remainder := ∑ c ∈ Finset.univ.erase c₀, q.compAlongOrderedFinpartition p c
  have hsplit : q.taylorComp p m = remainder + A.compContinuousMultilinearMap (p m) := by
    dsimp only [FormalMultilinearSeries.taylorComp, remainder]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c₀)]
    rw [inverseJet_coarse_term hm q p A hlinear]
  have hlead : ‖A.compContinuousMultilinearMap (p m)‖ ≤ 1 +
      ∑ c ∈ (Finset.univ.erase (inverseJetCoarse m hm)),
        B c.length * ∏ i : Fin c.length, P (c.partSize i) := by
    have heq : A.compContinuousMultilinearMap (p m) = q.taylorComp p m - remainder := by
      rw [hsplit]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add hidentity
      (inverseJet_remainder_bound hm q p B P hB hP hq hp))
  exact (inverseJet_norm_le_linear_image A hA (p m)).trans
    ((mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hlead hL))

end Yau.Proofs.C04Aux
