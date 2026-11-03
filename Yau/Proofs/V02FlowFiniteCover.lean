import Yau.Proofs.V03AtlasCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin

/-! Buffered finite charts from the original literal cotangent compact witness.
The common radius is chosen before any field or pointwise flow is considered. -/

open scoped Manifold Topology
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_cotangent_buffered_finite_cover {K : Set (CotangentPoint M)}
    (hK : CotangentCompact K) :
    ∃ (N : ℕ) (x : Fin N → M.Carrier) (a : Fin N → CotangentCoord n) (δ : ℝ),
      0 < δ ∧
      (∀ j, closedBall (a j) (8 * δ) ⊆ cotangentTarget (x j)) ∧
      K ⊆ ⋃ j, cotangentChartInv (x j) '' ball (a j) δ := by
  classical
  obtain ⟨r, x, C, hC, hK⟩ := hK
  have hε : ∀ i, ∃ ε : ℝ, 0 < ε ∧ cthickening ε (C i) ⊆ cotangentTarget (x i) :=
    fun i => (hC i).1.exists_cthickening_subset_open
      ((isOpen_extChartAt_target (I := ComplexModel n) (x i)).prod isOpen_univ) (hC i).2
  choose ε hεpos hεsub using hε
  let vals : Finset ℝ := insert 1 (Finset.univ.image ε)
  have hvals : vals.Nonempty := Finset.insert_nonempty _ _
  let μ := vals.min' hvals
  have hμ : 0 < μ := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact hεpos i
  let δ := μ / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : ∀ i, 8 * δ ≤ ε i := by
    intro i
    have hm : μ ≤ ε i := Finset.min'_le vals _ (by simp [vals])
    dsimp [δ]
    linarith
  have hcover : ∀ i, ∃ t : Finset (C i), C i ⊆ ⋃ c ∈ t, ball c.1 δ := by
    intro i
    apply (hC i).1.elim_finite_subcover (fun c : C i => ball c.1 δ) (fun _ => isOpen_ball)
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self hδ⟩
  choose t ht using hcover
  let J := Σ i : Fin r, {c : C i // c ∈ t i}
  let e := Fintype.equivFin J
  let x' : Fin (Fintype.card J) → M.Carrier := fun j => x (e.symm j).1
  let a' : Fin (Fintype.card J) → CotangentCoord n := fun j => (e.symm j).2.1.1
  refine ⟨Fintype.card J, x', a', δ, hδ, ?_, ?_⟩
  · intro j
    have hc : a' j ∈ C (e.symm j).1 := (e.symm j).2.1.2
    exact (closedBall_subset_closedBall (hδε (e.symm j).1)).trans
      ((closedBall_subset_cthickening hc _).trans (hεsub (e.symm j).1))
  · intro y hy
    rw [hK] at hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, rfl⟩ := hi
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (ht i hz)
    let j : J := ⟨i, c, hc⟩
    apply mem_iUnion.mpr
    refine ⟨e j, ?_⟩
    have hxj : x' (e j) = x i := by simp [x', j]
    have haj : a' (e j) = c.1 :=
      congrArg (fun q : J => q.2.1.1) (e.symm_apply_apply j)
    rw [hxj, haj]
    exact ⟨z, hzc, rfl⟩

end Yau.Blueprint.V02FlowProof
