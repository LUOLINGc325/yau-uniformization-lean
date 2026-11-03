import Yau.Proofs.F05UniformHolderGluing
import Yau.Proofs.F05HolderIntervals

/-! Compact local Hölder budgets give their own global value bound.
The resulting gluing constant precedes the moving endpoint and function. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem F05_uniform_compact_holder_glue_from_local {K : Set (Space n)}
    (hK : IsCompact K) {α : ℝ} (hα : 0 ≤ α) (S : ℝ)
    (r A : K → ℝ) (hr : ∀ i, 0 < r i) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → T ≤ S → ∀ (f : Point n → E) (P : ℝ), 0 ≤ P →
      (∀ i : K, HolderBound α (cylinder (K∩Metric.closedBall (i : Space n) (r i)) 0 T) f (A i*P)) →
      HolderBound α (cylinder K 0 T) f (C*P) := by
  classical
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun i : K => Metric.ball (i : Space n) (r i))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩)
  let B := 1+∑ i ∈ s,A i
  have hSum : 0 ≤ ∑ i ∈ s,A i := Finset.sum_nonneg (fun i hi => hA i)
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith
  have hB : 0 < B := zero_lt_one.trans_le hB1
  obtain ⟨C,hC,hGlue⟩ := F05_uniform_compact_holder_glue (E := E) hK hα S r A hr hA
  refine ⟨C*B,mul_pos hC hB,?_⟩
  intro T hT hTS f P hP hLocal
  have hPP : P ≤ B*P := by nlinarith
  have hSup : ∀ p ∈ cylinder K 0 T, ‖f p‖ ≤ B*P := by
    intro p hp
    obtain ⟨i,hi,hpi⟩ := mem_iUnion₂.mp (hs hp.1)
    have hAi : A i ≤ B := by
      have hSingle := Finset.single_le_sum (fun j hj => hA j) hi
      dsimp only [B]
      linarith
    exact ((hLocal i).2.1 p ⟨⟨hp.1,Metric.ball_subset_closedBall hpi⟩,hp.2⟩).trans
      (mul_le_mul_of_nonneg_right hAi hP)
  have hOut := hGlue T hT hTS f (B*P) (mul_nonneg hB.le hP) hSup
    (fun i => holderBound_mono_const (hLocal i) (mul_le_mul_of_nonneg_left hPP (hA i)))
  simpa only [mul_assoc] using hOut

theorem F05_uniform_compact_holder_glue_interval {K : Set (Space n)}
    (hK : IsCompact K) {α : ℝ} (hα : 0 ≤ α) (l S : ℝ)
    (r A : K → ℝ) (hr : ∀ i, 0 < r i) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, l ≤ T → T ≤ S → ∀ (f : Point n → E) (P : ℝ), 0 ≤ P →
      (∀ i : K, HolderBound α (cylinder (K∩Metric.closedBall (i : Space n) (r i)) l T) f (A i*P)) →
      HolderBound α (cylinder K l T) f (C*P) := by
  obtain ⟨C,hC,hGlue⟩ := F05_uniform_compact_holder_glue_from_local (E := E) hK hα (S-l) r A hr hA
  refine ⟨C,hC,?_⟩
  intro T hlT hTS f P hP hLocal
  have hLocalShift (i : K) : HolderBound α
      (cylinder (K∩Metric.closedBall (i : Space n) (r i)) 0 (T-l)) (timeTranslate l f) (A i*P) := by
    apply holderBound_timeTranslate_on_space
    simpa only [zero_add,sub_add_cancel] using hLocal i
  have hShift := hGlue (T-l) (sub_nonneg.mpr hlT) (sub_le_sub_right hTS l)
    (timeTranslate l f) P hP hLocalShift
  have hBack := holderBound_timeTranslate_on_space (l := l) (r := T) (τ := -l)
    (show HolderBound α (cylinder K (l+-l) (T+-l)) (timeTranslate l f) (C*P) by
      simpa only [add_neg_cancel,sub_eq_add_neg] using hShift)
  apply holderBound_congr_on hBack
  intro p hp
  simp only [timeTranslate,timeTranslatePoint,Prod.fst,Prod.snd,neg_add_cancel_right]

end Yau.Proofs.F05Aux
