import Yau.Proofs.F01ClosedTimeSpaceCommutation
import Yau.Proofs.F01ZeroExtensionParabolicC2

/-! The genuine scalar time equation differentiates in an actual
spatial direction at both closed faces. Zero initial value and zero initial
time jet then give the spatial derivative its own parabolic C2 zero extension. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closed_time_jet_smooth {f P : E × ℝ → F} {S : Set E} {T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 T))
    (hJet : ∀ x ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) (Icc 0 T) t) :
    ContDiffOn ℝ ∞ P (S ×ˢ Icc 0 T) := by
  apply (closed_slab_time_derivWithin_smooth hS (uniqueDiffOn_Icc hT) hf).congr
  intro p hp
  exact ((hJet p.1 hp.1 p.2 hp.2).derivWithin ((uniqueDiffOn_Icc hT) p.2 hp.2)).symm

theorem closed_space_direction_time_jet {f P : E × ℝ → F} {S : Set E} {T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 T))
    (hJet : ∀ x ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) (Icc 0 T) t)
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc 0 T) (v : E) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun z => f (z, s)) x v)
      (fderiv ℝ (fun z => P (z, t)) x v) (Icc 0 T) t := by
  have hG := closed_slab_space_direction_smooth hS (uniqueDiffOn_Icc hT) hf v
  have hcurve : ContDiffOn ℝ ∞ (fun s => fderiv ℝ (fun z => f (z, s)) x v) (Icc 0 T) :=
    hG.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨hx, hs⟩)
  have hd := (hcurve t ht).differentiableWithinAt (by simp) |>.hasDerivWithinAt
  have heq : (fun z => derivWithin (fun s => f (z, s)) (Icc 0 T) t) =ᶠ[𝓝 x]
      (fun z => P (z, t)) := by
    filter_upwards [hS.mem_nhds hx] with z hz
    exact (hJet z hz t ht).derivWithin ((uniqueDiffOn_Icc hT) t ht)
  have he := closed_time_space_derivative_commute hS hT hf hx ht v
  rw [heq.fderiv_eq] at he
  rw [he] at hd
  exact hd

theorem zero_extension_spatial_direction_C2 {n : ℕ}
    {f P : Yau.Parabolic.Point n → ℝ} {S : Set (Yau.Parabolic.Space n)} {a T : ℝ}
    (hS : IsOpen S) (hT : 0 < T) (ha : a < T) (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc 0 T))
    (hf0 : ∀ x ∈ S, f (x, 0) = 0) (hP0 : ∀ x ∈ S, P (x, 0) = 0)
    (hJet : ∀ x ∈ S, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => f (x, s)) (P (x, t)) (Icc 0 T) t)
    (v : Yau.Parabolic.Space n) :
    Yau.Parabolic.C2 (S ×ˢ Icc a T) (forwardZeroSpaceTime
      (fun p : Yau.Parabolic.Point n => fderiv ℝ (fun z => f (z, p.2)) p.1 v)) := by
  apply forwardZeroSpaceTime_parabolic_C2 hS hT ha
    (closed_slab_space_direction_smooth hS (uniqueDiffOn_Icc hT) hf v)
  · intro x hx
    have heq : (fun z => f (z, 0)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact hf0 z hz
    rw [heq.fderiv_eq]
    simp
  · intro x hx
    have hd := closed_space_direction_time_jet hS hT hf hJet hx ⟨le_rfl, hT.le⟩ v
    have heq : (fun z => P (z, 0)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hS.mem_nhds hx] with z hz
      exact hP0 z hz
    rw [heq.fderiv_eq] at hd
    simpa only [fderiv_const_apply, zero_apply] using hd

end Yau.NodeProofs.F01Aux
