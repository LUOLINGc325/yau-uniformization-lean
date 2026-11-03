import Yau.Proofs.P06TraceHilbertScalarHeat
import Yau.Proofs.P06TraceHilbertScalarL1
import Yau.Proofs.P06TraceHilbertResolvent
import Yau.Proofs.P06TracePairing

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}

def traceInitialLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) : Lp ℝ 2 μ :=
  (scalar_memLp g μ (formTrace g.form A) (trace_l2 g μ A hA h11)).toLp (formTrace g.form A)

theorem traceInitialLp_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) :
    traceInitialLp g μ A hA h11 =ᵐ[μ] formTrace g.form A :=
  (scalar_memLp g μ (formTrace g.form A) (trace_l2 g μ A hA h11)).coeFn_toLp

theorem scalarLift_traceInitialLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) :
    scalarLift g μ (traceInitialLp g μ A hA h11) =
      contraction g μ (realizeActualForm g μ A hA) := by
  rw [traceInitialLp, scalarLift_toLp, trace_realize g μ A hA h11]

def traceHeatLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : L2RealForm g.form μ A) (h11 : RealOneOne A) (t : ℝ) : Lp ℝ 2 μ :=
  scalarHeatFamily g μ hμ t (traceInitialLp g μ A hA h11)

/-- This scalar L² function is the contraction of the actual same-time
degree-two Hodge heat; its defining scalar formula is justified here. -/
theorem traceHeat_hilbert (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : L2RealForm g.form μ A) (h11 : RealOneOne A)
    (t : ℝ) (ht : 0 ≤ t) :
    scalarLift g μ (traceHeatLp g μ hμ A hA h11 t) =
      contraction g μ (hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA)) := by
  rw [traceHeatLp, scalarHeat_eq_hodgeHeat g μ hμ hk _ t ht,
    scalarLift_traceInitialLp, heat g μ hμ hk t ht]

theorem compact_trace_l1 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A) :
    Integrable (formTrace g.form A) μ := by
  have hi := smooth_compact_formInner_integrable g μ hμ A (omegaForm g.form) hA
    (omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)) hcA
  exact hi.congr (Filter.Eventually.of_forall fun x => (formTrace_eq_inner_omega g.form A h11 x).symm)

/-- The trace of the actual Hodge heat has the true global L¹ bound for
every positive compact smooth (1,1) initial datum. -/
theorem traceHeat_l1 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (h11 : RealOneOne A) (hp : FormLE 0 A) (t : ℝ) (ht : 0 ≤ t) :
    let hAL := smooth_compactlySupported_l2RealForm g μ hμ A hA hcA
    Integrable (traceHeatLp g μ hμ A hAL h11 t) μ ∧
      (∫ x, |traceHeatLp g μ hμ A hAL h11 t x| ∂μ) ≤ ∫ x, formTrace g.form A x ∂μ := by
  dsimp only
  let hAL := smooth_compactlySupported_l2RealForm g μ hμ A hA hcA
  let f := traceInitialLp g μ A hAL h11
  have hf : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [traceInitialLp_coe g μ A hAL h11] with x hx
    rw [hx]
    exact P06Aux.formTrace_nonnegative g.form A h11 hp x
  have hi : Integrable f μ := (compact_trace_l1 g μ hμ A hA hcA h11).congr
    (traceInitialLp_coe g μ A hAL h11).symm
  have hP := scalarHeat_l1_nonneg g μ hμ t ht f hf hi
  have hpos := scalarHeatFamily_nonneg g μ hμ ht f hf
  refine ⟨hP.1, ?_⟩
  change (∫ x, |scalarHeatFamily g μ hμ t f x| ∂μ) ≤ _
  calc
    _ = ∫ x, scalarHeatFamily g μ hμ t f x ∂μ :=
      integral_congr_ae (hpos.mono fun x hx => abs_of_nonneg hx)
    _ ≤ ∫ x, f x ∂μ := hP.2
    _ = _ := integral_congr_ae (traceInitialLp_coe g μ A hAL h11)

theorem trace_representative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A B : RealForm M 2) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B)
    (h11A : RealOneOne A) (h11B : RealOneOne B) (t : ℝ) (ht : 0 ≤ t)
    (hBheat : realizeActualForm g μ B hB = hodgeHeatHilbert g μ hμ 2 t (realizeActualForm g μ A hA)) :
    formTrace g.form B =ᵐ[μ] traceHeatLp g μ hμ A hA h11A t := by
  have hlift : scalarLift g μ (traceInitialLp g μ B hB h11B) =
      scalarLift g μ (traceHeatLp g μ hμ A hA h11A t) := by
    rw [scalarLift_traceInitialLp, hBheat, traceHeat_hilbert g μ hμ hk A hA h11A t ht]
  have he := scalarLift_injective g μ hlift
  exact (traceInitialLp_coe g μ B hB h11B).symm.trans (Filter.Eventually.of_forall
    (fun x => congrArg (fun q : Lp ℝ 2 μ => q x) he))

theorem trace_representative_l1 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A B : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (h11A : RealOneOne A) (hp : FormLE 0 A) (hB : L2RealForm g.form μ B)
    (h11B : RealOneOne B) (t : ℝ) (ht : 0 ≤ t)
    (hBheat : realizeActualForm g μ B hB = hodgeHeatHilbert g μ hμ 2 t
      (realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA))) :
    Integrable (formTrace g.form B) μ ∧
      (∫ x, |formTrace g.form B x| ∂μ) ≤ ∫ x, formTrace g.form A x ∂μ := by
  have he := trace_representative g μ hμ hk A B
    (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA) hB h11A h11B t ht hBheat
  have hi := traceHeat_l1 g μ hμ A hA hcA h11A hp t ht
  refine ⟨hi.1.congr he.symm, ?_⟩
  exact (integral_congr_ae (he.mono fun x hx => congrArg abs hx)).le.trans hi.2

end Yau.NodeProofs.P06Aux.TraceHilbert
