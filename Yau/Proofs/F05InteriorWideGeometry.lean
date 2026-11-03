import Yau.Proofs.F05HolderOscillationGeometry

/-! Full raw interior cylinders keep a fixed quarter-unit spatial buffer,
with no physical boundary. Their terminal face remains inside the native
closed cylinder, including when its center is at the terminal time. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_wide_oscCylinder_subsets {T : ℝ} {p : Point n}
    (hp : p ∈ cylinder (region none (5/2)) 0 T) {h ρ : ℝ} (hh : 0 < h)
    (hbt : h ≤ Real.sqrt p.2) (hρ : h ≤ ρ) (hρsmall : ρ ≤ 1/8) :
    dgOscCylinderOpen p (h/2) ⊆ F05CapOpen none (11/4) ×ˢ Ioo 0 T ∧
      dgOscCylinder p (h/2) ⊆ cylinder (region none (11/4)) 0 T ∧
      dgOscCylinder p (h/2) ⊆ cylinder (closure (F05CapOpen none (11/4))) 0 T := by
  have hsq : h^2 ≤ p.2 := by nlinarith [Real.sq_sqrt hp.2.1,Real.sqrt_nonneg p.2]
  have hbottom : 0 < p.2-(h/2)^2 := by nlinarith
  have hCap {z : Space n} (hz : z ∈ Metric.ball p.1 (h/2)) :
      z ∈ F05CapOpen none (11/4) := by
    have hzp : ‖z-p.1‖ < h/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
    have hn := norm_add_le (z-p.1) p.1
    rw [sub_add_cancel] at hn
    refine ⟨trivial,?_⟩
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hp.1.1]
  refine ⟨?_,?_,?_⟩
  · intro z hz
    exact ⟨hCap hz.1,hbottom.trans hz.2.1,hz.2.2.trans_le hp.2.2⟩
  · intro z hz
    have hNorm : ‖z.1‖ < 11/4 := by
      simpa only [Metric.mem_ball,dist_zero_right] using (hCap hz.1).2
    exact ⟨⟨hNorm.le,trivial⟩,(hbottom.trans hz.2.1).le,hz.2.2.trans hp.2.2⟩
  · intro z hz
    exact ⟨subset_closure (hCap hz.1),(hbottom.trans hz.2.1).le,hz.2.2.trans hp.2.2⟩

end Yau.Proofs.F05Aux
