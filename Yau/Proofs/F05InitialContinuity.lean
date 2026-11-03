import Yau.Proofs.F05FlowBarriers
import Yau.Proofs.F05SmoothContinuity

/-! The actual 0≤w≤rho barriers force the original zero initial value and
joint continuity through the initial face. No higher corner compatibility
or uniform estimates at remote exhaustion boundaries are required. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_majorant_initial_continuity (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) (w : STF X)
    (hSmooth : SmoothSpaceTime w (Ioo 0 T))
    (hBarrier : ∀ x t, t ∈ Ico 0 T → 0 ≤ w x t ∧ w x t ≤ ρ x t) :
    (∀ x, w x 0 = 0) ∧
      ContinuousOn (fun z : Pt X × ℝ => w z.1 z.2) (univ ×ˢ Ico 0 T) := by
  have hInitial (x : Pt X) : w x 0 = 0 := by
    have hBound := hBarrier x 0 ⟨le_rfl,hT⟩
    rw [Yau.F04Proof.rho_initial o h U P ρ hloc x] at hBound
    exact le_antisymm hBound.2 hBound.1
  refine ⟨hInitial,?_⟩
  have hWCont := F05_smooth_spacetime_continuousOn hSmooth
  have hRhoCont := F05_smooth_spacetime_continuousOn hloc.2.2.2.1
  intro z hz
  by_cases ht : z.2 = 0
  · have hSub : (univ : Set (Pt X)) ×ˢ Ico (0 : ℝ) T ⊆ (univ : Set (Pt X)) ×ˢ Ici 0 := fun y hy => ⟨hy.1,hy.2.1⟩
    have hRhoAt := (hRhoCont z (hSub hz)).mono hSub
    have hRho0 : ρ z.1 z.2 = 0 := by rw [ht]; exact Yau.F04Proof.rho_initial o h U P ρ hloc z.1
    have hW0 : w z.1 z.2 = 0 := by rw [ht]; exact hInitial z.1
    change Tendsto (fun y : Pt X × ℝ => w y.1 y.2) (𝓝[univ ×ˢ Ico 0 T] z) (𝓝 (w z.1 z.2))
    rw [hW0]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun y : Pt X × ℝ => ρ y.1 y.2) (𝓝[univ ×ˢ Ico 0 T] z) (𝓝 0) by
        simpa only [ContinuousWithinAt,hRho0] using hRhoAt)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hBarrier y.1 y.2 hy.2).1
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hBarrier y.1 y.2 hy.2).2
  · have hPos : 0 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm ht)
    have hAt := hWCont z ⟨hz.1,hPos,hz.2.2⟩
    apply hAt.mono_of_mem_nhdsWithin
    have hNear : {y : Pt X × ℝ | 0 < y.2} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hPos
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hNear] with y hy hyPos
    exact ⟨hy.1,hyPos,hy.2.2⟩

end Yau.Proofs.F05Aux
