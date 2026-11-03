import Yau.Proofs.P04CanonicalChartIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

noncomputable section
open Set MeasureTheory Metric
open scoped Topology

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs

/-- The exact pole exponent 2(n+1) is not integrable on any positive-radius
model ball. The positive-dimension input is obtained internally from M. -/
theorem norm_pole_not_integrableOn {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    ¬IntegrableOn (fun z : ComplexVector n => ‖z‖^(-2*((n : ℝ)+1)))
      (Metric.ball 0 r) (lebesgueC n) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : Nontrivial (ComplexVector n) := inferInstance
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  intro hint
  have H : IntegrableOn
      (fun t : ℝ => t^(Module.finrank ℝ (ComplexVector n)-1)*t^(-2*((n : ℝ)+1))) (Ioo 0 r) := by
    simpa only [smul_eq_mul] using
      (integrableOn_fun_norm_addHaar (lebesgueC n) (f := fun t : ℝ => t^(-2*((n : ℝ)+1)))).mp hint
  have heq : EqOn
      (fun t : ℝ => t^(Module.finrank ℝ (ComplexVector n)-1)*t^(-2*((n : ℝ)+1)))
      (fun t : ℝ => t^(-3 : ℝ)) (Ioo 0 r) := by
    intro t ht
    change t^(Module.finrank ℝ (ComplexVector n)-1)*t^(-2*((n : ℝ)+1))=t^(-3 : ℝ)
    rw [← Real.rpow_natCast t (Module.finrank ℝ (ComplexVector n)-1),← Real.rpow_add ht.1]
    congr 1
    rw [complexVector_finrank_real,Nat.cast_sub (by omega : 1 ≤ 2*n)]
    push_cast
    ring
  have hbad : IntegrableOn (fun t : ℝ => t^(-3 : ℝ)) (Ioo 0 r) :=
    H.congr_fun heq measurableSet_Ioo
  have Hexp := (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mp hbad
  norm_num at Hexp

end Yau.Proofs.P04Aux
