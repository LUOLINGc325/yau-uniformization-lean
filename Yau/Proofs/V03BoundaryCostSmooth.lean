import Yau.Proofs.V03TimeScalars
import Yau.Proofs.V03LogRadial

/-! Local smoothness of the full original boundary cost, including the
physical time and both reciprocal walls. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def boundaryDensity (d : VariationData X q) (j : ℕ) (F : VariationDisc X) (ζ : ℂ) : ℝ :=
  dualNorm (d.h (discTime F ζ)) (F.f ζ).1 (F.f ζ).2 +
    wallCost d j (F.f ζ) (discTime F ζ) F.s

theorem admissible_boundaryDensity_contDiffWithinAt {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (hy : F.f ζ ∈ boundaryRegion d j) :
    ContDiffWithinAt ℝ ∞ (boundaryDensity d j F) (Metric.closedBall 0 1) ζ := by
  have hp := setup_wallProfiles hd
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  have hu := cotangentDisc_smoothFn_contDiffOn hd.2.2.2.1.1 hF.1
  have h0 : d.h 0 = X.metric.form := hd.2.2.1.1.1.1
  have hN0 : ContDiffOn ℝ ∞ (fun η => dualNorm (d.h 0) (F.f η).1 (F.f η).2)
      (Metric.closedBall 0 1) := by
    rw [h0]
    exact cotangentDisc_dualNorm_contDiffOn X.metric hF.1
  have hdb : ContDiffOn ℝ ∞ (fun η => deltaBase d j (F.f η).1) (Metric.closedBall 0 1) :=
    hp.1.comp_contDiffOn (hu.div_const (d.A j))
  have hdf : ContDiffOn ℝ ∞ (fun η => deltaFiber d j (F.f η)) (Metric.closedBall 0 1) :=
    hp.2.1.comp_contDiffOn (hN0.div_const (d.B j ^ 2))
  have hwb : ContDiffWithinAt ℝ ∞ (fun η => wallBase d j (F.f η).1) (Metric.closedBall 0 1) ζ :=
    ((hdb ζ hζ).inv (deltaBase_pos hp hA hy.1).ne').sub contDiffWithinAt_const
  have hwf : ContDiffWithinAt ℝ ∞ (fun η => wallFiber d j (F.f η)) (Metric.closedBall 0 1) ζ :=
    ((hdf ζ hζ).inv (deltaFiber_pos hp hB hy.2).ne').sub contDiffWithinAt_const
  exact (admissible_metricNorm_contDiffOn hd hF ζ hζ).add
    ((admissible_baseCost_contDiffOn hd hF ζ hζ).add
      (contDiffWithinAt_const.mul (hwb.add hwf)))

theorem admissible_boundaryDensity_circle_contDiff {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (fun θ => boundaryDensity d j F (circlePoint θ)) := by
  have hf (θ : ℝ) : ContDiffWithinAt ℝ ∞ (boundaryDensity d j F) (Metric.closedBall 0 1)
      (((1 : ℝ) : ℂ) * circlePoint θ) := by
    simpa only [Complex.ofReal_one, one_mul] using
      admissible_boundaryDensity_contDiffWithinAt hd hF (circlePoint_mem_closedBall θ)
        (hF.2.2.2.2.2.2.2.1 θ)
  have hc := radial_trace_contDiff (r := 1) (by simp) hf
  simpa only [Complex.ofReal_one, one_mul] using hc

theorem radial_boundaryDensity_contDiff_eventually {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1,
      ContDiff ℝ ∞ (fun θ => boundaryDensity d j F ((r : ℂ) * circlePoint θ)) := by
  filter_upwards [self_mem_nhdsWithin, radial_boundaryRegion_eventually hd hF] with r hr hb
  apply radial_trace_contDiff hr
  intro θ
  exact admissible_boundaryDensity_contDiffWithinAt hd hF
    (radial_maps_closedBall hr.1 hr.2 (circlePoint_mem_closedBall θ)) (hb θ)

theorem boundaryCost_radial_eq (d : VariationData X q) (j : ℕ) (F : VariationDisc X) (r : ℝ) :
    boundaryCost d j (radialVariationDisc F r) =
      circleAverage (fun θ => boundaryDensity d j F ((r : ℂ) * circlePoint θ)) := rfl

end Yau.Blueprint.V03Proof
