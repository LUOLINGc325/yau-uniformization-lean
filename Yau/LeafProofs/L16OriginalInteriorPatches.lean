import Yau.LeafProofs.L16LocalizedSchauderBridge
import Yau.LeafProofs.L16HolderExtension
import Yau.LeafProofs.L16LocalTimeTransport
import Yau.LeafProofs.L16LowJetInterpolation

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def classicalInteriorPatch {n : ℕ} (δ h σ : ℝ) (hh : 0 < h)
    (c : Space n) (u : Point n → ℝ) (p : Point n) : ℝ :=
  initialTimeCutoff (localSchauderTime δ h) p.2*
    (innerPatchBump (h/8) (by positivity) c p.1*timeTranslate σ u p)

/-- Uniform genuine localized Schauder solutions constructed from the original
    frozen backward-cylinder hypotheses and a local low-jet Holder budget. -/
theorem exists_uniform_original_interior_patch_schauder {n : ℕ}
    {α M lam upper : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) :
    ∃ δ A : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < A ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      Elliptic (backward 2) a lam upper → HolderBound α (backward 2) a M →
      (∀ i, HolderBound α (backward 2) (fun p => b p i) M) →
      HolderBound α (backward 2) f F → C2 (backward 2) u →
      (∀ p ∈ backward 2, |u p| ≤ B) →
      (∀ p ∈ backward 2, linearOp (backward 2) a b u p = f p) →
      ∀ (r R τ : ℝ) (c : Space n) (L : ℝ) (_hr : 1 ≤ r) (hrR : r < R),
      R ≤ 3/2 → τ ∈ Set.Icc (-(r^2)) 0 → ‖c‖ ≤ r →
      HolderBound α (cylinder (Metric.closedBall 0 (r+3*(R-r)/4)) (-(R^2)) 0)
        (fun p => (u p,spatialD u p)) L →
      SchauderBound α (cylinder Set.univ 0 (localSchauderTime δ (R-r)))
        (classicalInteriorPatch δ (R-r) (τ-localSchauderTime δ (R-r))
          (sub_pos.mpr hrR) c u)
        (A*((R-r)⁻¹)^8*(F+L)) := by
  obtain ⟨M',K,hM',hK,hExtensions⟩ :=
    exists_uniform_backward_coefficient_extension (n := n) hα hα1 hM
  obtain ⟨δ,A,hδ,hδ1,hA,hBridge⟩ :=
    exists_uniform_localized_classical_schauder (n := n) (M := M')
      (lam := min lam 1) (upper := max upper 1) hα hα1 hM'.le hK
  refine ⟨δ,A,hδ,hδ1,hA,?_⟩
  intro a b f u F B hEll ha hb hf hu hB hPDE r R τ c L hr hrR hR hτ hc hLow
  obtain ⟨haExt,hbExt,hEllExt,hAgree,hExterior⟩ := hExtensions a b lam upper ha hb hEll
  let h : ℝ := R-r
  let S : ℝ := r+3*h/4
  let T : ℝ := localSchauderTime δ h
  let σ : ℝ := τ-T
  let O : Set (Space n) := Metric.ball 0 S
  let ae : Point n → Mat n := interiorHolderCoefficientExtension a
  let be : Point n → Yau.RIdx n → ℝ := interiorHolderDriftExtension b
  let as : Point n → Mat n := timeTranslate σ ae
  let bs : Point n → Yau.RIdx n → ℝ := timeTranslate σ be
  let fs : Point n → ℝ := timeTranslate σ f
  let us : Point n → ℝ := timeTranslate σ u
  have hh : 0 < h := sub_pos.mpr hrR
  have hh1 : h ≤ 1 := by dsimp only [h]; linarith
  have hS : S < R := by dsimp only [S,h]; linarith
  have hS2 : S < 2 := hS.trans (by linarith)
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hEnd : T+σ = τ := by dsimp only [σ]; ring
  have hTsmall : T ≤ h^2/8 := by
    dsimp only [T,localSchauderTime]
    exact div_le_div_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ1 (sq_nonneg h))
      (by norm_num)
  have hGap : T ≤ R^2-r^2 := by
    have hQuad : h^2/8 ≤ 2*h := by nlinarith
    have hSum : 2 ≤ R+r := by linarith
    have hScale := mul_le_mul_of_nonneg_left hSum hh.le
    have hId : R^2-r^2 = h*(R+r) := by dsimp only [h]; ring
    have hScale' : 2*h ≤ h*(R+r) := by nlinarith [hScale]
    exact hTsmall.trans (hQuad.trans (hScale'.trans_eq hId.symm))
  have hStart : -(R^2) ≤ σ := by dsimp only [σ]; linarith [hτ.1]
  have hσ3 : (-3 : ℝ) ≤ σ := by
    have hR0 : 0 ≤ R := by linarith
    have hSq : R^2 ≤ (3/2 : ℝ)^2 := pow_le_pow_left₀ hR0 hR 2
    linarith
  have hσ4 : -((2 : ℝ)^2) < σ := by linarith
  have hEnd0 : T+σ ≤ 0 := hEnd ▸ hτ.2
  have hσEnd : σ < T+σ := by linarith
  have hOSub : O ⊆ Metric.ball (0 : Space n) 2 :=
    Metric.ball_subset_ball hS2.le
  have hSourceSub : cylinder O σ (T+σ) ⊆ backward 2 :=
    cylinder_subset_backward hOSub hσ4 hEnd0
  have huLocal : C2 (cylinder O σ (T+σ)) u :=
    c2_backward_restrict hOSub hσ4 hEnd0 hσEnd hu
  have huShift : C2 (cylinder O 0 T) us := by
    apply c2_timeTranslate_on_space (O := O) (τ := σ) hT
    simpa only [zero_add] using huLocal
  have hfShift : HolderBound α (cylinder O 0 T) fs F := by
    apply holderBound_timeTranslate_on_space (O := O) (τ := σ)
    simpa only [zero_add] using holderBound_mono hf hSourceSub
  have hLowSource : HolderBound α (cylinder O σ (T+σ))
      (fun p => (u p,spatialD u p)) L := by
    apply holderBound_mono hLow
    intro p hp
    exact ⟨Metric.ball_subset_closedBall hp.1,hStart.trans hp.2.1,hp.2.2.trans hEnd0⟩
  have hLowShift : HolderBound α (cylinder O 0 T) (fun p => (us p,spatialD us p)) L := by
    change HolderBound α (cylinder O 0 T) (timeTranslate σ (fun p => (u p,spatialD u p))) L
    apply holderBound_timeTranslate_on_space (O := O) (τ := σ)
    simpa only [zero_add] using hLowSource
  have hCoeffA : HolderBound α (cylinder Set.univ 0 T) as M' := by
    apply holderBound_timeTranslate_on_space (O := Set.univ) (τ := σ)
    exact holderBound_mono haExt (Set.subset_univ _)
  have hCoeffB (i : Yau.RIdx n) :
      HolderBound α (cylinder Set.univ 0 T) (fun p => bs p i) M' := by
    change HolderBound α (cylinder Set.univ 0 T) (timeTranslate σ (fun p => be p i)) M'
    apply holderBound_timeTranslate_on_space (O := Set.univ) (τ := σ)
    exact holderBound_mono (hbExt i) (Set.subset_univ _)
  have hEllShift : Elliptic (cylinder Set.univ 0 T) as (min lam 1) (max upper 1) :=
    ⟨hEllExt.1,hEllExt.2.1,fun p hp => hEllExt.2.2 (timeTranslatePoint σ p) (Set.mem_univ _)⟩
  have hExteriorShift (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) (hx : p.1 ∉ K) :
      as p = 1 := (hExterior (timeTranslatePoint σ p) hx).1
  have hCoeffAgreement (p : Point n) (hp : p ∈ cylinder O σ (T+σ)) :
      ae p = a p ∧ ∀ i, be p i = b p i := by
    apply hAgree p
    refine ⟨?_,hσ3.trans hp.2.1,hp.2.2.trans hEnd0⟩
    have hx : ‖p.1‖ < S := by simpa only [O,Metric.mem_ball,dist_zero_right] using hp.1
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  have hPDELocal (p : Point n) (hp : p ∈ cylinder O σ (T+σ)) :
      linearOp (cylinder O σ (T+σ)) ae be u p = f p := by
    have hEq := hCoeffAgreement p hp
    have hbEq : be p = b p := funext hEq.2
    rw [show linearOp (cylinder O σ (T+σ)) ae be u p =
        linearOp (cylinder O σ (T+σ)) a b u p by simp only [linearOp,hEq.1,hbEq]]
    rw [linearOp_backward_restrict hOSub hσ4 hEnd0 hσEnd hu a b hp]
    exact hPDE p (hSourceSub hp)
  have hPDEShift (p : Point n) (hp : p ∈ cylinder O 0 T) :
      linearOp (cylinder O 0 T) as bs us p = fs p := by
    have hInput : C2 (cylinder O (0+σ) (T+σ)) u := by simpa only [zero_add] using huLocal
    rw [linearOp_timeTranslate_on_space hT hInput ae be hp]
    have hMapped : timeTranslatePoint σ p ∈ cylinder O σ (T+σ) := by
      simpa only [zero_add] using timeTranslatePoint_mem_cylinder_on_space (τ := σ) hp
    simpa only [zero_add,fs,timeTranslate] using hPDELocal (timeTranslatePoint σ p) hMapped
  have hZeroMem : ((0,0) : Point n) ∈ backward 2 := by
    norm_num [backward,Metric.mem_ball]
  have hB0 : 0 ≤ B := (abs_nonneg (u (0,0))).trans (hB (0,0) hZeroMem)
  have hBoundShift (p : Point n) (hp : p ∈ cylinder O 0 T) : |us p| ≤ B := by
    apply hB (timeTranslatePoint σ p)
    apply hSourceSub
    simpa only [zero_add] using timeTranslatePoint_mem_cylinder_on_space (τ := σ) hp
  have hSupport :
      tsupport (innerPatchBump (h/8) (by positivity) c : Space n → ℝ) ⊆ O := by
    intro y hy
    change y ∈ closure (Function.support (innerPatchBump (h/8) (by positivity) c : Space n → ℝ)) at hy
    rw [(innerPatchBump (h/8) (by positivity) c).support_eq] at hy
    have hyClosed := Metric.closure_ball_subset_closedBall hy
    have hyNorm : ‖y-c‖ ≤ 3*(h/8)/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,innerPatchBump] using hyClosed
    change y ∈ Metric.ball 0 S
    rw [Metric.mem_ball,dist_zero_right]
    have hTri := norm_add_le (y-c) c
    rw [sub_add_cancel] at hTri
    dsimp only [S]
    linarith
  have hPatch := hBridge h hh hh1 c O as bs fs us F L B
    Metric.isOpen_ball hCoeffA hCoeffB hEllShift hExteriorShift hSupport hLowShift hfShift
    huShift hB0 hBoundShift hPDEShift
  exact hPatch.1

end Yau.LeafProofs.L16Aux
