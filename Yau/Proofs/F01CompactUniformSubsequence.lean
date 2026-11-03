import spec.CHAIN.CONTRACTS
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! A genuine common compact-range bound and actual equicontinuity give
a uniformly convergent subsequence on a compact domain. -/
noncomputable section
open Set Filter
open scoped BoundedContinuousFunction
namespace Yau.NodeProofs.F01Aux
variable {A F : Type*} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup F] [ProperSpace F]

theorem compact_uniform_family_closure
    (u : ℕ → A →ᵇ F) (hEqui : Equicontinuous (fun m x => u m x))
    {B : ℝ} (hB : ∀ m x, ‖u m x‖ ≤ B) : IsCompact (closure (range u)) := by
  let chooseIndex : range u → ℕ := fun v => Classical.choose v.property
  have hchoose (v : range u) : u (chooseIndex v) = v.val := Classical.choose_spec v.property
  have hEquiRange : Equicontinuous (fun v : range u => fun x => v.val x) := by
    convert hEqui.comp chooseIndex using 1
    funext v x
    exact congrArg (fun f : A →ᵇ F => f x) (hchoose v).symm
  exact BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : F) B)
      (isCompact_closedBall _ _) (range u) (by
        intro f x hf
        obtain ⟨m, rfl⟩ := hf
        simpa only [Metric.mem_closedBall, dist_zero_right] using hB m x) hEquiRange

theorem compact_uniform_subsequence_of_equicontinuous
    (u : ℕ → A →ᵇ F) (hEqui : Equicontinuous (fun m x => u m x))
    {B : ℝ} (hB : ∀ m x, ‖u m x‖ ≤ B) :
    ∃ v : A →ᵇ F, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformly (fun m x => u (σ m) x) (fun x => v x) atTop := by
  obtain ⟨v, hv, σ, hσ, hconv⟩ := (compact_uniform_family_closure u hEqui hB).tendsto_subseq
    (fun m => subset_closure (mem_range_self m))
  exact ⟨v, σ, hσ, BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv⟩

end Yau.NodeProofs.F01Aux
