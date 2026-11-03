import Yau.Proofs.F01PotentialClockRHS
import Yau.Proofs.F01PotentialClockContinuity
import Yau.Proofs.F01ClosedFaceClockPaste
import Yau.Proofs.F01SlabSpatialTensorClock

/-! A positive potential solution with a continuous terminal spatial
jet tower pastes smoothly to an actual short-time solution with the
same terminal value. All mixed derivatives are consequences. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem potential_closed_face_paste_smooth
    (f g b : Point n → ℝ) (S : Point n → Matrix (Fin n) (Fin n) ℂ)
    {O : Set (Space n)} {l T r : ℝ} (hO : IsOpen O) (hlT : l < T) (hTr : T < r)
    (hS : ContDiffOn ℝ ∞ S (O ×ˢ Ioo l r))
    (hb : ContDiffOn ℝ ∞ b (O ×ˢ Ioo l r))
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Ioo l T))
    (hg : ContDiffOn ℝ ∞ g (O ×ˢ Ico T r))
    (hSlices : ∀ t ∈ Ioc l T, ContDiffOn ℝ ∞ (fun z => f (z, t)) O)
    (hContinuous : ∀ k, ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) (O ×ˢ Ioc l T))
    (hMatch : ∀ x ∈ O, f (x, T) = g (x, T))
    (hPosLeft : ∀ p ∈ O ×ˢ Ioc l T,
      0 < (S p + leviC (fun z => f (z, p.2)) p.1).det.re)
    (hPosRight : ∀ p ∈ O ×ˢ Ico T r,
      0 < (S p + leviC (fun z => g (z, p.2)) p.1).det.re)
    (hLeft : ∀ x ∈ O, ∀ t ∈ Ioo l T,
      HasDerivWithinAt (fun s => f (x, s))
        (localPotentialClockRHS S b f (x, t)) (Ioo l T) t)
    (hRight : ∀ x ∈ O, ∀ t ∈ Ico T r,
      HasDerivWithinAt (fun s => g (x, s))
        (localPotentialClockRHS S b g (x, t)) (Ico T r) t) :
    ContDiffOn ℝ ∞ (timeFacePaste f g T) (O ×ˢ Ioo l r) := by
  have hAL : O ×ˢ Ioc l T ⊆ O ×ˢ Ioo l r :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans_lt hTr⟩
  have hAR : O ×ˢ Ico T r ⊆ O ×ˢ Ioo l r :=
    fun p hp => ⟨hp.1, hlT.trans_le hp.2.1, hp.2.2⟩
  have hSS (t : ℝ) (ht : t ∈ Ioo l r) : ContDiffOn ℝ ∞ (fun z => S (z, t)) O :=
    hS.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  have hBS (t : ℝ) (ht : t ∈ Ioo l r) : ContDiffOn ℝ ∞ (fun z => b (z, t)) O :=
    hb.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  have hGS (t : ℝ) (ht : t ∈ Ico T r) : ContDiffOn ℝ ∞ (fun z => g (z, t)) O :=
    hg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  have hPL (t : ℝ) (ht : t ∈ Ioo l T) :
      ContDiffOn ℝ ∞ (fun z => localPotentialClockRHS S b f (z, t)) O :=
    localPotentialClockRHS_smooth_slice S b f hO t
      (hSS t ⟨ht.1, ht.2.trans hTr⟩) (hBS t ⟨ht.1, ht.2.trans hTr⟩)
      (hSlices t ⟨ht.1, ht.2.le⟩) (fun z hz => hPosLeft (z, t) ⟨hz, ht.1, ht.2.le⟩)
  have hPR (t : ℝ) (ht : t ∈ Ico T r) :
      ContDiffOn ℝ ∞ (fun z => localPotentialClockRHS S b g (z, t)) O :=
    localPotentialClockRHS_smooth_slice S b g hO t
      (hSS t ⟨hlT.trans_le ht.1, ht.2⟩) (hBS t ⟨hlT.trans_le ht.1, ht.2⟩)
      (hGS t ht) (fun z hz => hPosRight (z, t) ⟨hz, ht⟩)
  have hDenseL : ∀ t ∈ Ioo l T, t ∈ closure (interior (Ioo l T)) := by
    intro t ht
    rw [interior_Ioo]
    exact subset_closure ht
  have hDenseR : ∀ t ∈ Ico T r, t ∈ closure (interior (Ico T r)) := by
    intro t ht
    rw [interior_Ico, closure_Ioo hTr.ne]
    exact ⟨ht.1, ht.2.le⟩
  have hClock (k : ℕ) : ∀ p ∈ O ×ˢ Ioo l r,
      HasDerivAt (fun t => iteratedFDeriv ℝ k
        (fun z => timeFacePaste f g T (z, t)) p.1)
        (iteratedFDeriv ℝ k (fun z =>
          localPotentialClockRHS S b (timeFacePaste f g T) (z, p.2)) p.1) p.2 := by
    have hPC : ContinuousOn
        (fun p => iteratedFDeriv ℝ k (fun z => localPotentialClockRHS S b f (z, p.2)) p.1)
        (O ×ˢ Ioc l T) :=
      potential_spatial_clock_jet_continuousOn f b S hO isOpen_Ioo hS hb hAL
        (fun p hp => hSlices p.2 hp.2) hContinuous hPosLeft k
    have hh := closed_face_clock_equations_paste
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1)
      (fun p => iteratedFDeriv ℝ k (fun z => g (z, p.2)) p.1)
      (fun p => iteratedFDeriv ℝ k (fun z => localPotentialClockRHS S b f (z, p.2)) p.1)
      (fun p => iteratedFDeriv ℝ k (fun z => localPotentialClockRHS S b g (z, p.2)) p.1)
      hlT hTr
      (fun x hx => spatial_jet_face_match f g hO T hMatch k hx)
      (fun x hx => spatial_jet_face_match (localPotentialClockRHS S b f)
        (localPotentialClockRHS S b g) hO T
        (fun z hz => localPotentialClockRHS_face_match S b f g hO T hMatch hz) k hx)
      (hContinuous k) hPC
      (fun x hx t ht => (slab_spatial_tensor_time_jet hO (uniqueDiffOn_Ioo l T)
        hDenseL hf hPL hLeft k hx ht).hasDerivAt (isOpen_Ioo.mem_nhds ht))
      (fun x hx t ht => slab_spatial_tensor_time_jet hO (uniqueDiffOn_Ico T r)
        hDenseR hg hPR hRight k hx ht)
    intro p hp
    have hv := hh p hp
    rw [← spatial_clock_rhs_timeFacePaste S b f g T k p] at hv
    simpa only [← spatial_jet_timeFacePaste] using hv
  apply (joint_smooth_of_potential_tensor_clock_equations (timeFacePaste f g T) b S
    hO isOpen_Ioo hS hb ?_ ?_ ?_ hClock).1
  · intro t ht
    by_cases hh : t ≤ T
    · simpa only [timeFacePaste, if_pos hh] using hSlices t ⟨ht.1, hh⟩
    · simpa only [timeFacePaste, if_neg hh] using hGS t ⟨(not_le.mp hh).le, ht.2⟩
  · intro k
    exact continuousOn_spatial_jet_timeFacePaste f g hO hMatch k (hContinuous k)
      (slab_spatial_tensor_smooth hO (uniqueDiffOn_Ico T r) hg k).continuousOn
  · intro p hp
    by_cases hh : p.2 ≤ T
    · simpa only [timeFacePaste, if_pos hh] using hPosLeft p ⟨hp.1, hp.2.1, hh⟩
    · simpa only [timeFacePaste, if_neg hh] using hPosRight p ⟨hp.1, (not_le.mp hh).le, hp.2.2⟩

end Yau.NodeProofs.F01Aux
