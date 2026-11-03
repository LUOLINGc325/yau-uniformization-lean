import Yau.LeafProofs.L16NearPairHolder

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- One fixed interior scale supplies actual low-jet, raw high-jet and
    localized Schauder bounds with a common constant before all PDE data. -/
theorem exists_fixed_interior_schauder_family {n : ℕ} {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      Elliptic (backward 2) a lam upper → HolderBound α (backward 2) a M →
      (∀ i, HolderBound α (backward 2) (fun p => b p i) M) →
      HolderBound α (backward 2) f F → C2 (backward 2) u →
      (∀ p ∈ backward 2, |u p| ≤ B) →
      (∀ p ∈ backward 2, linearOp (backward 2) a b u p = f p) →
      let h : ℝ := (5/4)-1
      let S : ℝ := 1+3*h/4
      let T := localSchauderTime δ h
      HolderBound α (cylinder (Metric.closedBall 0 S) (-((5/4 : ℝ)^2)) 0)
        (fun p => (u p,spatialD u p)) (C*(B+F)) ∧
      (∀ p ∈ closedBackwardCylinder (n := n) (5/4), originalHighJetSize u p ≤ C*(B+F)) ∧
      ∀ (τ : ℝ) (c : Space n), τ ∈ Set.Icc (-1 : ℝ) 0 → ‖c‖ ≤ 1 →
        SchauderBound α (cylinder Set.univ 0 T)
          (classicalInteriorPatch δ h (τ-T) (by norm_num) c u) (C*(B+F)) := by
  obtain ⟨CK,hCK,hHigh⟩ := exists_uniform_original_high_jet_bound
    (n := n) (M := M) (lam := lam) (upper := upper) hα hα1 hM
  obtain ⟨δ,A,hδ,hδ1,hA,hPatches⟩ := exists_uniform_original_interior_patch_schauder
    (n := n) (M := M) (lam := lam) (upper := upper) hα hα1 hM
  let R : ℝ := 5/4
  let h : ℝ := R-1
  let S : ℝ := 1+3*h/4
  let ρ : ℝ := h/8
  let T : ℝ := localSchauderTime δ h
  let L0 : ℝ := 8*(ρ^(1-α)*CK+ρ^(-1-α))
  let W : ℝ := A*(h⁻¹)^8*(1+L0)
  let C : ℝ := 1+L0+CK+W
  have hh : 0 < h := by norm_num [h,R]
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by norm_num [ρ,h,R]
  have hL0 : 0 ≤ L0 := by dsimp only [L0]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hL0C : L0 ≤ C := by dsimp only [C]; linarith
  have hCKC : CK ≤ C := by dsimp only [C]; linarith
  have hWC : W ≤ C := by dsimp only [C]; linarith
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro a b f u F B hEll ha hb hf hu hB hPDE
  dsimp only
  let D : ℝ := B+F
  have hB0 : 0 ≤ B := by
    have hZero : ((0,0) : Point n) ∈ backward 2 := by norm_num [backward,Metric.mem_ball]
    exact (abs_nonneg (u (0,0))).trans (hB (0,0) hZero)
  have hD : 0 ≤ D := add_nonneg hB0 hf.1
  have hBLe : B ≤ D := le_add_of_nonneg_right hf.1
  have hFLe : F ≤ D := le_add_of_nonneg_left hB0
  have hRaw := hHigh a b f u F B hEll ha hb hf hu hB hPDE
  have hClosedSub : Metric.closedBall (0 : Space n) R ⊆ Metric.ball 0 2 := by
    intro x hx
    have hNorm : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    rw [Metric.mem_ball,dist_zero_right]
    norm_num [R] at hNorm
    linarith
  have hLower : -((2 : ℝ)^2) < -(R^2) := by norm_num [R]
  have hLen : -(R^2) < (0 : ℝ) := by norm_num [R]
  have hSub : closedBackwardCylinder (n := n) R ⊆ backward 2 :=
    cylinder_subset_backward hClosedSub hLower le_rfl
  have huClosed : C2 (closedBackwardCylinder (n := n) R) u :=
    c2_backward_restrict hClosedSub hLower le_rfl hLen hu
  have hK : ∀ p ∈ closedBackwardCylinder (n := n) R,
      ‖spatialDD u p‖ ≤ CK*D ∧ |timeD (closedBackwardCylinder R) u p| ≤ CK*D := by
    intro p hp
    refine ⟨(le_max_left _ _).trans (hRaw p hp),?_⟩
    change |timeD (cylinder (Metric.closedBall 0 R) (-(R^2)) 0) u p| ≤ _
    rw [timeD_backward_restrict hClosedSub hLower le_rfl hLen hu hp]
    exact (le_max_right _ _).trans (hRaw p hp)
  have hLowRaw := c2_lowPair_interpolation hα hα1 hLen
    (show 0 ≤ S by norm_num [S,h,R]) hρ hρ1
    (show S+ρ ≤ R by norm_num [S,ρ,h,R]) hB0 (mul_nonneg hCK.le hD) huClosed
    (fun p hp => hB p (hSub hp)) hK
  have hLow : HolderBound α (cylinder (Metric.closedBall 0 S) (-(R^2)) 0)
      (fun p => (u p,spatialD u p)) (L0*D) := by
    apply holderBound_mono_const hLowRaw
    have hScale := mul_le_mul_of_nonneg_left hBLe (Real.rpow_nonneg hρ.le (-1-α))
    dsimp only [L0]
    nlinarith
  refine ⟨holderBound_mono_const hLow (mul_le_mul_of_nonneg_right hL0C hD),?_,?_⟩
  · intro p hp
    exact (hRaw p hp).trans (mul_le_mul_of_nonneg_right hCKC hD)
  · intro τ c hτ hc
    have hPatch := hPatches a b f u F B hEll ha hb hf hu hB hPDE
      1 R τ c (L0*D) (by norm_num) (by norm_num [R])
      (by norm_num [R]) (by simpa only [one_pow,neg_mul] using hτ) hc hLow
    apply schauderBound_mono_const hPatch
    have hSource : F+L0*D ≤ (1+L0)*D := by nlinarith
    have hBudget := mul_le_mul_of_nonneg_left hSource
      (by positivity : 0 ≤ A*(h⁻¹)^8)
    calc
      _ ≤ W*D := by convert hBudget using 1; dsimp only [W]; ring
      _ ≤ C*D := mul_le_mul_of_nonneg_right hWC hD

end Yau.LeafProofs.L16Aux

namespace Yau.LeafProofs.L16InteriorLinear
open Yau.Parabolic Yau.ParabolicCandidates
open Yau.LeafProofs.L16Aux

theorem interiorLinearSchauder : InteriorLinearSchauder := by
  intro n hn α lam upper M hα hα1 hM
  obtain ⟨δ,C0,hδ,hδ1,hC0,hFamily⟩ := exists_fixed_interior_schauder_family
    (n := n) (M := M) (lam := lam) (upper := upper) hα hα1 hM.le
  let h : ℝ := (5/4)-1
  let T : ℝ := localSchauderTime δ h
  let εx : ℝ := h/16
  let εt : ℝ := T/4
  let CH : ℝ := 2*C0+2*C0*εx^(-α)+2*C0*εt^(-α/2)
  let C : ℝ := 1+C0+CH
  have hh : 0 < h := by norm_num [h]
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hTValue : T = δ/128 := by dsimp only [T,localSchauderTime,h]; ring
  have hT1 : T ≤ 1 := by rw [hTValue]; linarith
  have hεx : 0 < εx := by dsimp only [εx]; positivity
  have hεt : 0 < εt := by dsimp only [εt]; positivity
  have hCH : 0 ≤ CH := by dsimp only [CH]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC0C : C0 ≤ C := by dsimp only [C]; linarith
  have hCHC : CH ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro a b f u F B hEll ha hb hf hu hB hPDE
  obtain ⟨hLow,hRaw,hPatches⟩ := hFamily a b f u F B hEll ha hb hf hu hB hPDE
  let D : ℝ := B+F
  let Q : Set (Point n) := closedBackwardCylinder 1
  let H : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ) × ℝ :=
    fun p => (spatialDD u p,timeD (backward 2) u p)
  have hB0 : 0 ≤ B := by
    have hZero : ((0,0) : Point n) ∈ backward 2 := by norm_num [backward,Metric.mem_ball]
    exact (abs_nonneg (u (0,0))).trans (hB (0,0) hZero)
  have hD : 0 ≤ D := add_nonneg hB0 hf.1
  have hQSub : Q ⊆ closedBackwardCylinder (n := n) (5/4) :=
    closedBackwardCylinder_mono (by norm_num) (by norm_num)
  have hSup (p : Point n) (hp : p ∈ Q) : ‖H p‖ ≤ C0*D := by
    change originalHighJetSize u p ≤ _
    exact hRaw p (hQSub hp)
  have hNear : ∀ p ∈ Q, ∀ q ∈ Q, ‖p.1-q.1‖ ≤ εx → |p.2-q.2| ≤ εt →
      ‖H p-H q‖ ≤ (C0*D)*holderWeight α p q := by
    intro p hp q hq hSpace hTime
    let τ : ℝ := max p.2 q.2
    let σ : ℝ := τ-T
    let w : Point n → ℝ := classicalInteriorPatch δ h σ hh p.1 u
    have hpTime : (-1 : ℝ) ≤ p.2 := by simpa only [one_pow] using hp.2.1
    have hqTime : (-1 : ℝ) ≤ q.2 := by simpa only [one_pow] using hq.2.1
    have hτ : τ ∈ Set.Icc (-1 : ℝ) 0 :=
      ⟨hpTime.trans (le_max_left _ _),max_le hp.2.2 hq.2.2⟩
    have hCenter : ‖p.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    have hPatch : SchauderBound α (cylinder Set.univ 0 T) w (C0*D) :=
      hPatches τ p.1 hτ hCenter
    have hpτ : p.2 ≤ τ := le_max_left _ _
    have hqτ : q.2 ≤ τ := le_max_right _ _
    have hPMinusQ : p.2-q.2 ≤ T/4 := (le_abs_self _).trans hTime
    have hQMinusP : q.2-p.2 ≤ T/4 :=
      (le_abs_self _).trans (by simpa only [abs_sub_comm] using hTime)
    have hτP : τ ≤ p.2+T/4 := max_le (by linarith) (by linarith)
    have hτQ : τ ≤ q.2+T/4 := max_le (by linarith) (by linarith)
    have hpNormalized : p.2-σ ∈ Set.Icc 0 T := by
      constructor <;> dsimp only [σ] <;> linarith
    have hqNormalized : q.2-σ ∈ Set.Icc 0 T := by
      constructor <;> dsimp only [σ] <;> linarith
    have hpPlateau : T/2 < p.2-σ := by dsimp only [σ]; linarith
    have hqPlateau : T/2 < q.2-σ := by dsimp only [σ]; linarith
    have hσ : -((2 : ℝ)^2) < σ := by dsimp only [σ]; linarith [hτ.1]
    have hEnd : T+σ ≤ 0 := by dsimp only [σ]; linarith [hτ.2]
    have hpSpace : ‖p.1-p.1‖ < h/8 := by simp; positivity
    have hqSpace : ‖q.1-p.1‖ < h/8 := by
      have hBound : ‖q.1-p.1‖ ≤ h/16 := by simpa only [norm_sub_rev] using hSpace
      linarith
    have hRecover (z : Point n) (hz : z ∈ Q)
        (hzTime : z.2-σ ∈ Set.Icc 0 T) (hzPlateau : T/2 < z.2-σ)
        (hzSpace : ‖z.1-p.1‖ < h/8) :
        (spatialDD w (z.1,z.2-σ),
          timeD (cylinder Set.univ 0 T) w (z.1,z.2-σ)) = H z := by
      have hzBall : z.1 ∈ Metric.ball (0 : Space n) 2 := by
        have hNorm : ‖z.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
        rw [Metric.mem_ball,dist_zero_right]
        linarith
      apply Prod.ext
      · change spatialDD (classicalInteriorPatch δ h σ hh p.1 u) (z.1,z.2-σ) = spatialDD u z
        rw [classicalInteriorPatch_spatialDD_on_plateau hδ hh p.1 u hzPlateau.le hzSpace]
        simp only [sub_add_cancel,Prod.eta]
      · change timeD (cylinder Set.univ 0 T)
          (classicalInteriorPatch δ h σ hh p.1 u) (z.1,z.2-σ) = timeD (backward 2) u z
        rw [classicalInteriorPatch_timeD_on_plateau hδ hh p.1 u hzPlateau hzSpace,
          timeD_timeTranslate_backward_on_slab hT hσ hEnd hzTime hzBall hu]
        simp only [sub_add_cancel,Prod.eta]
    have hHighPatch : HolderBound α (cylinder Set.univ 0 T)
        (fun z => (spatialDD w z,timeD (cylinder Set.univ 0 T) w z)) (C0*D) := by
      refine ⟨mul_nonneg hC0.le hD,?_,?_⟩
      · intro z hz
        exact max_le (hPatch.2.2.2.1.2.1 z hz) (hPatch.2.2.2.2.2.1 z hz)
      · intro z hz v hv
        exact max_le (hPatch.2.2.2.1.2.2 z hz v hv) (hPatch.2.2.2.2.2.2 z hz v hv)
    have hBound := hHighPatch.2.2 (p.1,p.2-σ) ⟨Set.mem_univ _,hpNormalized⟩
      (q.1,q.2-σ) ⟨Set.mem_univ _,hqNormalized⟩
    change ‖(spatialDD w (p.1,p.2-σ),timeD (cylinder Set.univ 0 T) w (p.1,p.2-σ))-
        (spatialDD w (q.1,q.2-σ),timeD (cylinder Set.univ 0 T) w (q.1,q.2-σ))‖ ≤ _ at hBound
    rw [hRecover p hp hpNormalized hpPlateau hpSpace,
      hRecover q hq hqNormalized hqPlateau hqSpace] at hBound
    have hTimeDiff : (p.2-σ)-(q.2-σ) = p.2-q.2 := by ring
    have hWeight : holderWeight α (p.1,p.2-σ) (q.1,q.2-σ) = holderWeight α p q := by
      simp only [holderWeight,hTimeDiff]
    rw [hWeight] at hBound
    exact hBound
  have hPair := holderBound_of_near_pairs (f := H) (Q := Q) hα.le (mul_nonneg hC0.le hD)
    (mul_nonneg hC0.le hD) hεx hεt hSup hNear
  have hBudget :
      C0*D+C0*D+2*(C0*D)*εx^(-α)+2*(C0*D)*εt^(-α/2) = CH*D := by
    dsimp only [CH]
    ring
  rw [hBudget] at hPair
  have hBackSub : backward (n := n) 1 ⊆ Q := by
    intro p hp
    exact ⟨Metric.ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2⟩
  have hBackLow : backward (n := n) 1 ⊆
      cylinder (Metric.closedBall 0 (1+3*h/4)) (-((5/4 : ℝ)^2)) 0 := by
    intro p hp
    refine ⟨Metric.closedBall_subset_closedBall (show (1 : ℝ) ≤ 1+3*h/4 by linarith [hh])
      (Metric.ball_subset_closedBall hp.1),?_,hp.2.2⟩
    have hStart : -((5/4 : ℝ)^2) ≤ -((1 : ℝ)^2) := by norm_num
    exact hStart.trans hp.2.1.le
  have hLowBack := holderBound_mono hLow hBackLow
  have hHess := holderBound_mono (holderBound_fst hPair) hBackSub
  have hTimeOrig := holderBound_mono (holderBound_snd hPair) hBackSub
  have hTimeActual : HolderBound α (backward 1) (timeD (backward 1) u) (CH*D) := by
    apply holderBound_congr_on hTimeOrig
    intro p hp
    exact (timeD_backward_restrict_radius (by norm_num) (by norm_num) hu hp).symm
  have hScale : CH*D ≤ C*D := mul_le_mul_of_nonneg_right hCHC hD
  refine ⟨c2_backward_restrict_radius (by norm_num) (by norm_num) hu,
    mul_nonneg hC.le hD,?_,holderBound_mono_const hHess hScale,
    holderBound_mono_const hTimeActual hScale⟩
  intro p hp
  have hLowPoint := hLowBack.2.1 p hp
  have hValue : |u p| ≤ C0*D := (le_max_left ‖u p‖ ‖spatialD u p‖).trans hLowPoint
  have hGradient : ‖spatialD u p‖ ≤ C0*D := (le_max_right ‖u p‖ ‖spatialD u p‖).trans hLowPoint
  have hLowScale := mul_le_mul_of_nonneg_right hC0C hD
  exact ⟨hValue.trans hLowScale,hGradient.trans hLowScale⟩

end Yau.LeafProofs.L16InteriorLinear
