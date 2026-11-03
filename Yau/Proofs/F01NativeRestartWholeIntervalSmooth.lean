import Yau.Proofs.F01NativeRestartPasteIdentity
import Yau.Proofs.F01SpaceTimeLocalTimeCover

/-! The actual old subhorizons and the smooth terminal join cover one
strictly longer closed interval, including its original initial face. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem native_restart_paste_smooth_extended_interval
    (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ) (W : M.Carrier → ℝ → ℝ)
    {T δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hU : ∀ s, 0 ≤ s → s < T → SmoothSpaceTime U (Icc 0 s))
    (hJoin : SmoothSpaceTime (nativePastedRestartPotential U u W T) (Ioo (T - δ) (T + ε))) :
    SmoothSpaceTime (nativePastedRestartPotential U u W T) (Icc 0 (T + ε / 2)) := by
  apply smoothSpaceTime_of_local_time_cover
  intro t ht
  by_cases hh : t < T
  · let θ : ℝ := (t + T) / 2
    have htθ : t < θ := by dsimp only [θ]; linarith
    have hθT : θ < T := by dsimp only [θ]; linarith
    have hθ0 : 0 ≤ θ := ht.1.trans htθ.le
    refine ⟨Icc 0 θ, ⟨ht.1, htθ.le⟩, ?_, ?_⟩
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htθ), self_mem_nhdsWithin]
        with s hsθ hs
      exact ⟨hs.1, hsθ.le⟩
    · intro a
      apply (hU θ hθ0 hθT a).congr
      intro p hp
      exact nativePastedRestartPotential_before U u W T _ (hp.2.2.trans_lt hθT)
  · have hTt : T ≤ t := le_of_not_gt hh
    have htJ : t ∈ Ioo (T - δ) (T + ε) := by
      constructor <;> linarith [ht.2]
    exact ⟨Ioo (T - δ) (T + ε), htJ,
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htJ), hJoin⟩

end Yau.NodeProofs.F01Aux
