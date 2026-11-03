import Yau.Proofs.F05HolderCaps
import Yau.LeafProofs.L16ExpBoundaryHolderGeometry

/-! Interior DG cylinders retain both fixed spatial buffers and the actual
physical half-space. The full-space case uses its constant gauge directly. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_gauge_positive_mem_flat {k : Option (RIdx n)} {x : Space n}
    (hx : 0 < F05FaceGauge k x) : x ∈ F05FlatOpen k := by
  cases k with
  | none => trivial
  | some j => exact neg_pos.mp hx

theorem F05_buffered_oscCylinder_subsets {k : Option (RIdx n)} {T : ℝ} {p : Point n}
    (hp : p ∈ cylinder (region k (3/2)) 0 T) {h ρ : ℝ} (hh : 0 < h)
    (hbd : h ≤ F05FaceGauge k p.1) (hbt : h ≤ Real.sqrt p.2)
    (hρ : h ≤ ρ) (hρsmall : ρ ≤ 1/8) :
    dgOscCylinderOpen p (h/2) ⊆ F05CapOpen k 2 ×ˢ Ioo 0 T ∧
      dgOscCylinder p (h/2) ⊆ cylinder (region k (7/4)) 0 T ∧
      dgOscCylinder p (h/2) ⊆ cylinder (closure (F05CapOpen k 2)) 0 T := by
  have hR : 0 < h/2 := by positivity
  have hxFlat : p.1 ∈ F05FlatOpen k := F05_gauge_positive_mem_flat (hh.trans_le hbd)
  have hBall := F05FaceGauge_ball_subset hxFlat (by linarith : h/2 ≤ F05FaceGauge k p.1)
  have hsqrt := Real.sq_sqrt hp.2.1
  have hsq : h^2 ≤ p.2 := by nlinarith [Real.sqrt_nonneg p.2]
  have hbottom : 0 < p.2-(h/2)^2 := by nlinarith
  have hNorm {z : Space n} (hz : z ∈ Metric.ball p.1 (h/2)) : ‖z‖ < 7/4 := by
    have hzp : ‖z-p.1‖ < h/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
    have hn := norm_add_le (z-p.1) p.1
    rw [sub_add_cancel] at hn
    linarith [hp.1.1]
  have hCap {z : Space n} (hz : z ∈ Metric.ball p.1 (h/2)) : z ∈ F05CapOpen k 2 :=
    ⟨hBall hz,by rw [Metric.mem_ball,dist_zero_right]; linarith [hNorm hz]⟩
  refine ⟨?_,?_,?_⟩
  · intro z hz
    exact ⟨hCap hz.1,hbottom.trans hz.2.1,hz.2.2.trans_le hp.2.2⟩
  · intro z hz
    have hFlat : z.1 ∈ closure (F05FlatOpen k) := subset_closure (hBall hz.1)
    have hRegion : z.1 ∈ region k (7/4) := by
      refine ⟨(hNorm hz.1).le,?_⟩
      cases k <;> simpa only [F05FlatOpen_closure,mem_ofPred_eq] using hFlat
    exact ⟨hRegion,(hbottom.trans hz.2.1).le,hz.2.2.trans hp.2.2⟩
  · intro z hz
    exact ⟨subset_closure (hCap hz.1),(hbottom.trans hz.2.1).le,hz.2.2.trans hp.2.2⟩

end Yau.Proofs.F05Aux
