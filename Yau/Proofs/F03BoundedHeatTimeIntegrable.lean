import Yau.Proofs.F03BoundedInitialFaceProducer
import Yau.Proofs.F02Elementary

/-! Genuine bounded scalar heat is time-integrable through the initial endpoint without a Hodge premise. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ} {M : ComplexManifold n}

theorem boundedScalarHeat_time_intervalIntegrable
    (g : HermitianField M) (f : M.Carrier → ℝ) (w : ℝ → M.Carrier → ℝ)
    (hw : IsBoundedScalarHeat g f w) {R : ℝ} (hR : 0 ≤ R) (x : M.Carrier) :
    IntervalIntegrable (fun b => w b x) volume 0 R := by
  obtain ⟨C,_hC,hBound⟩ := hw.2.2.1 (R+1) (by linarith)
  have hCont : ContinuousOn (fun b => w b x) (Ioc 0 R) :=
    (F02Aux.timeSlice_continuousOn hw.1 x).mono (fun _ hb => hb.1)
  have hFin : (volume : Measure ℝ) (Ioc (0:ℝ) R) ≠ ⊤ :=
    ((measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
  apply (show IntegrableOn (fun _ : ℝ => C) (Ioc 0 R) volume from integrableOn_const hFin).mono'
    (hCont.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with b hb
  simpa only [Real.norm_eq_abs] using hBound x b hb.1 (by linarith [hb.2])

end Yau.Proofs.F03Aux
