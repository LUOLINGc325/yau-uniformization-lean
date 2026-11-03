import Yau.LeafProofs.L05MongeTimeTransport

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic L16Aux

theorem timeTranslatePoint_neg_cancel {n : ℕ} (tau : ℝ) (p : Point n) :
    timeTranslatePoint tau (timeTranslatePoint (-tau) p)=p := by
  ext <;> simp only [timeTranslatePoint,add_assoc,neg_add_cancel,add_zero]

theorem monge_positive_shift_mem {n : ℕ} {p : Point n}
    (hp : p ∈ Metric.ball 0 (1/2:ℝ) ×ˢ Set.Ioc (0:ℝ) (1/4)) :
    timeTranslatePoint (-(1/4:ℝ)) p ∈ backward (1/2) := by
  refine ⟨hp.1,?_,?_⟩
  · change -((1/2:ℝ)^2) < p.2+(-(1/4:ℝ))
    linarith only [hp.2.1]
  · change p.2+(-(1/4:ℝ)) ≤ 0
    linarith only [hp.2.2]

set_option maxHeartbeats 1400000 in
theorem schauderBound_initial_of_shifted {n : ℕ} {gamma C : ℝ} (hgamma : 0 < gamma)
    {u : Point n → ℝ} (hu : C2 (cylinder (Metric.ball 0 1) (-1) 1) u)
    (hz : ∀ p ∈ cylinder (Metric.ball 0 1) (-1) 1, p.2 ≤ 0 → u p=0)
    (hshift : SchauderBound gamma (backward (1/2)) (timeTranslate (1/4:ℝ) u) C) :
    SchauderBound gamma (cylinder (Metric.ball 0 (1/2)) (-(1/4)) (1/4)) u C := by
  have hO : Metric.ball (0 : Space n) (1/2:ℝ) ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (by norm_num)
  have hQ : cylinder (Metric.ball (0 : Space n) (1/2)) (-(1/4)) (1/4) ⊆
      cylinder (Metric.ball 0 1) (-1) 1 := by
    intro p hp
    exact ⟨hO hp.1,(by linarith only [hp.2.1]),(by linarith only [hp.2.2])⟩
  have huSmall := c2_cylinder_restrict_on_space (by norm_num : (-(1/4):ℝ) < 1/4)
    hO (by norm_num : (-1:ℝ) ≤ -(1/4)) (by norm_num : (1/4:ℝ) ≤ 1) hu
  apply schauderBound_across_zero Metric.isOpen_ball (by norm_num : (0:ℝ) < 1/4) hgamma
    huSmall (fun p hp ht => hz p (hQ hp) ht) hshift.2.1
  · intro p hp
    have hh := hshift.2.2.1 _ (monge_positive_shift_mem hp)
    simpa only [spatialD_timeTranslate,timeTranslate,timeTranslatePoint,
      add_assoc,neg_add_cancel,add_zero] using hh
  · have hh := holderBound_timeTranslate_set (fun p hp => monge_positive_shift_mem hp) hshift.2.2.2.1
    apply holderBound_congr_on hh
    intro p hp
    change spatialDD (timeTranslate (1/4:ℝ) u) (timeTranslatePoint (-(1/4:ℝ)) p)=spatialDD u p
    rw [spatialDD_timeTranslate,timeTranslatePoint_neg_cancel]
  · have hh := holderBound_timeTranslate_set (fun p hp => monge_positive_shift_mem hp) hshift.2.2.2.2
    apply holderBound_congr_on hh
    intro p hp
    have ht := timeD_timeTranslate_backward_buffer hO
      (by norm_num : (-1:ℝ) < -((1/2)^2)+(1/4)) (by norm_num : (1/4:ℝ) < 1)
      hu (monge_positive_shift_mem hp)
    rw [timeTranslatePoint_neg_cancel] at ht
    change timeD (backward (1/2)) (timeTranslate (1/4:ℝ) u) (timeTranslatePoint (-(1/4:ℝ)) p)=_
    exact ht.trans (timeD_cylinder_restrict_on_space (by norm_num : (-(1/4):ℝ) < 1/4)
      hO (by norm_num : (-1:ℝ) ≤ -(1/4)) (by norm_num : (1/4:ℝ) ≤ 1) hu
      ⟨hp.1,(by linarith only [hp.2.1]),hp.2.2⟩).symm

end Yau.LeafProofs.L05Aux
