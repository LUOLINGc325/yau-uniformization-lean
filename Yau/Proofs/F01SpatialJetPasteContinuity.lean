import Yau.Proofs.F01TimeFacePaste

/-! Agreement of the actual terminal slice forces agreement of every
spatial jet. The two continuous closed-face jet towers then paste. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_jet_face_match
    (f g : E × ℝ → F) {O : Set E} (hO : IsOpen O) (T : ℝ)
    (hMatch : ∀ x ∈ O, f (x, T) = g (x, T))
    (k : ℕ) {x : E} (hx : x ∈ O) :
    iteratedFDeriv ℝ k (fun z => f (z, T)) x =
      iteratedFDeriv ℝ k (fun z => g (z, T)) x := by
  have he : (fun z => f (z, T)) =ᶠ[𝓝 x] (fun z => g (z, T)) := by
    filter_upwards [hO.mem_nhds hx] with z hz using hMatch z hz
  exact (he.iteratedFDeriv ℝ k).self_of_nhds

theorem continuousOn_spatial_jet_timeFacePaste
    (f g : E × ℝ → F) {O : Set E} (hO : IsOpen O) {l T r : ℝ}
    (hMatch : ∀ x ∈ O, f (x, T) = g (x, T)) (k : ℕ)
    (hf : ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) (O ×ˢ Ioc l T))
    (hg : ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1) (O ×ˢ Ico T r)) :
    ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun z => timeFacePaste f g T (z, p.2)) p.1)
      (O ×ˢ Ioo l r) := by
  have hh := timeFacePaste_continuousOn
    (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1)
    (fun p => iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1) T (O ×ˢ Ioo l r)
    (hf.mono (fun p hp => ⟨hp.1.1, hp.1.2.1, hp.2⟩))
    (hg.mono (fun p hp => ⟨hp.1.1, hp.2, hp.1.2.2⟩))
    (fun p hp he => by
      rw [he]
      exact spatial_jet_face_match f g hO T hMatch k hp.1)
  simpa only [spatial_jet_timeFacePaste] using hh

end Yau.NodeProofs.F01Aux
