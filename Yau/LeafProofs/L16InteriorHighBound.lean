import Yau.LeafProofs.L16InteriorHighEstimate
import Yau.LeafProofs.L16RadiusAbsorption

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The original classical equation has a uniform compact interior bound for
    its actual Hessian and time derivative. No Holder norm is assumed finite. -/
theorem exists_uniform_original_high_jet_bound {n : ℕ} {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      Elliptic (backward 2) a lam upper → HolderBound α (backward 2) a M →
      (∀ i, HolderBound α (backward 2) (fun p => b p i) M) →
      HolderBound α (backward 2) f F → C2 (backward 2) u →
      (∀ p ∈ backward 2, |u p| ≤ B) →
      (∀ p ∈ backward 2, linearOp (backward 2) a b u p = f p) →
      ∀ p ∈ closedBackwardCylinder (n := n) (5/4),
        originalHighJetSize u p ≤ C*(B+F) := by
  obtain ⟨A,hA,hRaw⟩ := exists_uniform_original_high_jet_estimate
    (n := n) (M := M) (lam := lam) (upper := upper) hα hα1 hM
  obtain ⟨P,C,hC,hRadius⟩ := exists_radius_absorption_parameters hα hα1 hA
  refine ⟨2*C*(8 : ℝ)^P,by positivity,?_⟩
  intro a b f u F B hEll ha hb hf hu hB hPDE
  have hB0 : 0 ≤ B := by
    have hZero : ((0,0) : Point n) ∈ backward 2 := by norm_num [backward,Metric.mem_ball]
    exact (abs_nonneg (u (0,0))).trans (hB (0,0) hZero)
  obtain ⟨Kstar,hKstar,hInit⟩ := exists_compact_original_high_jet_bound hu
  apply nested_high_bound_absorption (P := P) (A := C) (D := B+F)
    (Kstar := Kstar) hC.le (add_nonneg hB0 hf.1) hKstar.le hInit
  intro r R K hr hrR hR hK hBound p hp
  let h : ℝ := R-r
  have hh : 0 < h := sub_pos.mpr hrR
  have hh1 : h ≤ 1 := by dsimp only [h]; linarith
  obtain ⟨ρ,hρ,hρ1,hMargin,hAbsorb⟩ := hRadius h hh hh1
  have hEstimate := hRaw a b f u F B hEll ha hb hf hu hB hPDE
    r R ρ K hr hrR hR hρ hρ1 hMargin hK hBound p hp
  exact hEstimate.trans (hAbsorb K B F hK hB0 hf.1)

end Yau.LeafProofs.L16Aux
