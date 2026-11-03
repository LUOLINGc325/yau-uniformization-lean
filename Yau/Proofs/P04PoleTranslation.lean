import Yau.Proofs.P04PoleNonintegrability

noncomputable section
open Set MeasureTheory Metric
open scoped Topology

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs

theorem norm_pole_not_integrableOn_at {n : ℕ} (hn : 0 < n) (z₀ : ComplexVector n)
    {r : ℝ} (hr : 0 < r) :
    ¬IntegrableOn (fun z : ComplexVector n => ‖z-z₀‖^(-2*((n : ℝ)+1)))
      (Metric.ball z₀ r) (lebesgueC n) := by
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  intro hint
  have H := (measurePreserving_add_right (lebesgueC n) z₀).integrableOn_comp_preimage
    (Homeomorph.addRight z₀).measurableEmbedding |>.mpr hint
  have hpre : (fun x : ComplexVector n => x+z₀) ⁻¹' Metric.ball z₀ r=Metric.ball 0 r := by
    ext x
    simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero]
  apply norm_pole_not_integrableOn hn hr
  simpa only [Function.comp_def,add_sub_cancel_right,hpre] using H

end Yau.Proofs.P04Aux
