import Yau.Proofs.F01TerminalTimeJetPasting

/-! Explicit pasting across one clock face. Continuity uses the two
closed half domains and agreement on the face; spatial jets commute
with this pasting because its branch depends only on time. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def timeFacePaste (f g : E × ℝ → F) (T : ℝ) (p : E × ℝ) : F :=
  if p.2 ≤ T then f p else g p

theorem timeFacePaste_right {f g : E × ℝ → F} {x : E} {T s : ℝ}
    (hMatch : f (x, T) = g (x, T)) (hs : T ≤ s) :
    timeFacePaste f g T (x, s) = g (x, s) := by
  by_cases hh : s ≤ T
  · have he : s = T := le_antisymm hh hs
    simpa [timeFacePaste, he] using hMatch
  · exact if_neg hh

theorem timeFacePaste_continuousOn (f g : E × ℝ → F) (T : ℝ) (W : Set (E × ℝ))
    (hf : ContinuousOn f (W ∩ {p | p.2 ≤ T}))
    (hg : ContinuousOn g (W ∩ {p | T ≤ p.2}))
    (hMatch : ∀ p ∈ W, p.2 = T → f p = g p) :
    ContinuousOn (timeFacePaste f g T) W := by
  have hClosed : IsClosed {p : E × ℝ | p.2 ≤ T} :=
    isClosed_le continuous_snd continuous_const
  apply ContinuousOn.if
  · intro p hp
    exact hMatch p hp.1 ((frontier_le_subset_eq continuous_snd continuous_const) hp.2)
  · exact hf.mono (by
      intro p hp
      exact ⟨hp.1, hClosed.closure_eq ▸ hp.2⟩)
  · apply hg.mono
    intro p hp
    refine ⟨hp.1, ?_⟩
    exact closure_minimal (fun q hq => (not_le.mp hq).le)
      (isClosed_le continuous_const continuous_snd) hp.2

theorem spatial_jet_timeFacePaste (f g : E × ℝ → F) (T : ℝ) (k : ℕ) (p : E × ℝ) :
    iteratedFDeriv ℝ k (fun z => timeFacePaste f g T (z, p.2)) p.1 =
      timeFacePaste
        (fun q => iteratedFDeriv ℝ k (fun z => f (z, q.2)) q.1)
        (fun q => iteratedFDeriv ℝ k (fun z => g (z, q.2)) q.1) T p := by
  by_cases ht : p.2 ≤ T
  · simp only [timeFacePaste, if_pos ht]
  · simp only [timeFacePaste, if_neg ht]

theorem timeFacePaste_hasDerivAt_face (f g : E × ℝ → F) (x : E) (T : ℝ) (v : F)
    (hMatch : f (x, T) = g (x, T))
    (hf : HasDerivWithinAt (fun t => f (x, t)) v (Iic T) T)
    (hg : HasDerivWithinAt (fun t => g (x, t)) v (Ici T) T) :
    HasDerivAt (fun t => timeFacePaste f g T (x, t)) v T := by
  apply time_jet_of_matching_closed_faces
  · exact hf.congr_of_mem (fun t ht => if_pos ht) (by simp)
  · exact hg.congr_of_mem (fun t ht => timeFacePaste_right hMatch ht) (by simp)

end Yau.NodeProofs.F01Aux
