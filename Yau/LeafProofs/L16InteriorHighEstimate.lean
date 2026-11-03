import Yau.LeafProofs.L16InteriorPatchJets
import Yau.LeafProofs.L16NestedAbsorption

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def originalHighJetSize {n : ℕ} (u : Point n → ℝ) (p : Point n) : ℝ :=
  max ‖spatialDD u p‖ |timeD (backward 2) u p|

/-- A uniform estimate for the genuine highest jets, derived from the original
    equation using only finite compact raw bounds and low-jet interpolation. -/
theorem exists_uniform_original_high_jet_estimate {n : ℕ} {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      Elliptic (backward 2) a lam upper → HolderBound α (backward 2) a M →
      (∀ i, HolderBound α (backward 2) (fun p => b p i) M) →
      HolderBound α (backward 2) f F → C2 (backward 2) u →
      (∀ p ∈ backward 2, |u p| ≤ B) →
      (∀ p ∈ backward 2, linearOp (backward 2) a b u p = f p) →
      ∀ r R ρ K : ℝ, 1 ≤ r → r < R → R ≤ 3/2 →
      0 < ρ → ρ ≤ 1 → ρ ≤ (R-r)/4 → 0 ≤ K →
      (∀ p ∈ closedBackwardCylinder (n := n) R, originalHighJetSize u p ≤ K) →
      ∀ p ∈ closedBackwardCylinder (n := n) r,
        originalHighJetSize u p ≤
          A*((R-r)⁻¹)^8*(F+8*(ρ^(1-α)*K+ρ^(-1-α)*B)) := by
  obtain ⟨δ,A,hδ,hδ1,hA,hPatches⟩ :=
    exists_uniform_original_interior_patch_schauder (n := n) (M := M)
      (lam := lam) (upper := upper) hα hα1 hM
  refine ⟨A,hA,?_⟩
  intro a b f u F B hEll ha hb hf hu hB hPDE r R ρ K hr hrR hR hρ hρ1 hρMargin hK hHigh
  let h : ℝ := R-r
  let S : ℝ := r+3*h/4
  have hh : 0 < h := sub_pos.mpr hrR
  have hh1 : h ≤ 1 := by dsimp only [h]; linarith
  have hR0 : 0 < R := by linarith
  have hR2 : R < 2 := by linarith
  have hSqR : R^2 ≤ (3/2 : ℝ)^2 := pow_le_pow_left₀ hR0.le hR 2
  have hLower : -((2 : ℝ)^2) < -(R^2) := by linarith
  have hLen : -(R^2) < (0 : ℝ) := neg_neg_of_pos (sq_pos_of_pos hR0)
  have hClosedSub : Metric.closedBall (0 : Space n) R ⊆ Metric.ball 0 2 := by
    intro x hx
    rw [Metric.mem_ball,dist_zero_right]
    exact (show ‖x‖ ≤ R from by simpa only [Metric.mem_closedBall,dist_zero_right] using hx).trans_lt hR2
  have hSub : closedBackwardCylinder (n := n) R ⊆ backward 2 :=
    cylinder_subset_backward hClosedSub hLower le_rfl
  have huClosed : C2 (closedBackwardCylinder (n := n) R) u :=
    c2_backward_restrict hClosedSub hLower le_rfl hLen hu
  have hB0 : 0 ≤ B := by
    have hZero : ((0,0) : Point n) ∈ backward 2 := by norm_num [backward,Metric.mem_ball]
    exact (abs_nonneg (u (0,0))).trans (hB (0,0) hZero)
  have hRaw : ∀ p ∈ closedBackwardCylinder (n := n) R,
      ‖spatialDD u p‖ ≤ K ∧ |timeD (closedBackwardCylinder R) u p| ≤ K := by
    intro p hp
    refine ⟨(le_max_left _ _).trans (hHigh p hp),?_⟩
    change |timeD (cylinder (Metric.closedBall 0 R) (-(R^2)) 0) u p| ≤ K
    rw [timeD_backward_restrict hClosedSub hLower le_rfl hLen hu hp]
    exact (le_max_right _ _).trans (hHigh p hp)
  let L : ℝ := 8*(ρ^(1-α)*K+ρ^(-1-α)*B)
  have hLow : HolderBound α (cylinder (Metric.closedBall 0 S) (-(R^2)) 0)
      (fun p => (u p,spatialD u p)) L := by
    apply c2_lowPair_interpolation hα hα1 hLen (by dsimp only [S]; linarith) hρ hρ1
      (by dsimp only [S,h]; linarith) hB0 hK huClosed
      (fun p hp => hB p (hSub hp)) hRaw
  intro p hp
  let T : ℝ := localSchauderTime δ h
  let σ : ℝ := p.2-T
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hTδ : T ≤ δ := by
    have hBound : h^2/8 ≤ 1 := by nlinarith
    calc
      T = δ*(h^2/8) := by dsimp only [T,localSchauderTime]; ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left hBound hδ.le
      _ = δ := mul_one _
  have hT1 : T ≤ 1 := hTδ.trans hδ1
  have hr0 : 0 ≤ r := by linarith
  have hrUpper : r ≤ 3/2 := hrR.le.trans hR
  have hSqr : r^2 ≤ (3/2 : ℝ)^2 := pow_le_pow_left₀ hr0 hrUpper 2
  have hσ4 : -((2 : ℝ)^2) < σ := by
    have hTime : -(r^2) ≤ p.2 := hp.2.1
    dsimp only [σ]
    linarith
  have hEnd : T+σ = p.2 := by dsimp only [σ]; ring
  have hEnd0 : T+σ ≤ 0 := hEnd ▸ hp.2.2
  have hc : ‖p.1‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
  have hc2 : p.1 ∈ Metric.ball (0 : Space n) 2 := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith
  have hPatch := hPatches a b f u F B hEll ha hb hf hu hB hPDE
    r R p.2 p.1 L hr hrR hR hp.2 hc hLow
  have hpTop : ((p.1,T) : Point n) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hT.le,le_rfl⟩
  have hHess := hPatch.2.2.2.1.2.1 (p.1,T) hpTop
  have hTime := hPatch.2.2.2.2.2.1 (p.1,T) hpTop
  change ‖spatialDD (classicalInteriorPatch δ h σ hh p.1 u) (p.1,T)‖ ≤ _ at hHess
  change ‖timeD (cylinder Set.univ 0 T)
    (classicalInteriorPatch δ h σ hh p.1 u) (p.1,T)‖ ≤ _ at hTime
  rw [classicalInteriorPatch_spatialDD_at_top hδ hh p.1 u,hEnd] at hHess
  rw [classicalInteriorPatch_timeD_at_top hδ hh p.1 u,
    timeD_timeTranslate_backward_at_top hT hσ4 hEnd0 hc2 hu,hEnd] at hTime
  change max ‖spatialDD u p‖ |timeD (backward 2) u p| ≤ _
  exact max_le (by simpa only [Prod.eta] using hHess)
    (by simpa only [Real.norm_eq_abs,Prod.eta] using hTime)

/-- The finite starting bound follows directly from the original continuous
    genuine jets on one fixed compact cylinder. -/
theorem exists_compact_original_high_jet_bound {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 2) u) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ closedBackwardCylinder (n := n) (3/2),
      originalHighJetSize u p ≤ K := by
  have hSpace : Metric.closedBall (0 : Space n) (3/2) ⊆ Metric.ball 0 2 := by
    intro x hx
    have hNorm : ‖x‖ ≤ 3/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    rw [Metric.mem_ball,dist_zero_right]
    linarith
  have hSub : closedBackwardCylinder (n := n) (3/2) ⊆ backward 2 :=
    cylinder_subset_backward hSpace (by norm_num) le_rfl
  have hCompact : IsCompact (closedBackwardCylinder (n := n) (3/2)) :=
    (isCompact_closedBall (0 : Space n) (3/2)).prod isCompact_Icc
  obtain ⟨C,hC⟩ := hCompact.exists_bound_of_continuousOn (f := spatialDD u) (hu.2.2.1.mono hSub)
  obtain ⟨D,hD⟩ := hCompact.exists_bound_of_continuousOn (f := timeD (backward 2) u) (hu.2.2.2.1.mono hSub)
  refine ⟨1+|C|+|D|,by positivity,?_⟩
  intro p hp
  change max ‖spatialDD u p‖ |timeD (backward 2) u p| ≤ _
  exact max_le ((hC p hp).trans (by linarith [le_abs_self C,abs_nonneg D]))
    ((hD p hp).trans (by linarith [le_abs_self D,abs_nonneg C]))

end Yau.LeafProofs.L16Aux
