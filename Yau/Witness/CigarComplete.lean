import Yau.Witness.CigarField
import Yau.Witness.CigarProperExhaustion
import Yau.Proofs.C07ShortLiftIntegral

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Witness.Cigar

open Set Filter MeasureTheory

set_option backward.isDefEq.respectTransparency false

local instance : AddCommGroup V := (inferInstance : NormedAddCommGroup V).toAddCommGroup

/-- A smooth proper exhaustion for the genuine cigar length metric. -/
def cigarExhaustion (z : V) : ℝ :=
  Real.log (cigarDenom z) / 2

theorem cigar_exhaustion_hasFDerivAt (z : V) :
    HasFDerivAt cigarExhaustion
      ((cigarDenom z)⁻¹ • innerSL ℝ z) z := by
  change HasFDerivAt (fun p : V => Real.log (1 + ‖p‖ ^ 2) / 2)
    ((1 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z
  exact logNorm_hasFDerivAt z

theorem cigar_exhaustion_fderiv (z w : V) :
    fderiv ℝ cigarExhaustion z w = inner ℝ z w / cigarDenom z := by
  rw [(cigar_exhaustion_hasFDerivAt z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem cigar_exhaustion_speed_bound (z w : V) :
    |fderiv ℝ cigarExhaustion z w| ≤ ‖w‖ / Real.sqrt (cigarDenom z) := by
  rw [cigar_exhaustion_fderiv]
  exact logNorm_derivative_bound z w

theorem cigar_exhaustion_continuous : Continuous cigarExhaustion :=
  continuous_iff_continuousAt.2 fun z => (cigar_exhaustion_hasFDerivAt z).continuousAt

/-- Every admitted piecewise smooth curve controls the exhaustion difference,
including curves whose derivatives fail at their finite corner set. -/
theorem cigar_exhaustion_curveLength {x y : cigarPlane.Carrier}
    (γ : IntegrableCurve cigarField x y) :
    |cigarExhaustion x - cigarExhaustion y| ≤ curveLength cigarField γ.1 := by
  have hγ (t : ℝ) (hts : t ∉ γ.1.breakpoints) :
      DifferentiableAt ℝ (F := V) γ.1.toFun t := by
    have h := (γ.1.piecewise_c1 t hts).differentiableAt (by simp)
    change DifferentiableAt ℝ (fun s => chartPt (γ.1 t) (γ.1 s)) t at h
    simpa only [cigar_chartPt] using h
  have hdiff (t : ℝ) (hts : t ∉ γ.1.breakpoints) :
      HasDerivAt (fun s => cigarExhaustion (γ.1 s))
        (fderiv ℝ cigarExhaustion (γ.1 t) (deriv (F := V) γ.1.toFun t)) t := by
    exact (cigar_exhaustion_hasFDerivAt (γ.1 t)).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt t (hγ t hts).hasDerivAt
  have hB : IntervalIntegrable (curveSpeed cigarField γ.1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 γ.2
  have h := Yau.Proofs.C07ShortLiftAux.norm_sub_le_integral_except_finset
    γ.1.breakpoints zero_le_one
    (cigar_exhaustion_continuous.comp_continuousOn γ.1.continuous_on)
    (fun t _ hts => (hdiff t hts).differentiableAt)
    (fun t _ hts => by
      change ‖deriv (fun s => cigarExhaustion (γ.1 s)) t‖ ≤ curveSpeed cigarField γ.1 t
      rw [(hdiff t hts).deriv, Real.norm_eq_abs, cigar_curveSpeed]
      exact cigar_exhaustion_speed_bound (γ.1 t) (deriv (F := V) γ.1.toFun t)) hB
  simp only [Function.comp_apply] at h
  rw [γ.1.finish_eq, γ.1.start_eq, Real.norm_eq_abs,
    abs_sub_comm, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- Taking the infimum over all admissible curves preserves the common
exhaustion lower bound. -/
theorem cigar_exhaustion_distance (x y : cigarPlane.Carrier) :
    |cigarExhaustion x - cigarExhaustion y| ≤ inducedDistance cigarField x y := by
  unfold inducedDistance
  apply le_csInf
  · obtain ⟨γ⟩ := Yau.LeafProofs.L23Aux.integrable_curve_nonempty
      cigarField cigar_metricSmooth x y
    exact ⟨curveLength cigarField γ.1, ⟨γ, rfl⟩⟩
  · rintro _ ⟨γ, rfl⟩
    exact cigar_exhaustion_curveLength γ

/-- Compactness here is in the original Euclidean topology. -/
theorem cigar_exhaustion_sublevel_compact (B : ℝ) :
    IsCompact {z : cigarPlane.Carrier | cigarExhaustion z ≤ B} := by
  exact logNorm_sublevel_compact (E := V) B

/-- The distance defined by the lengths of the actual cigar field is complete. -/
theorem cigar_completeDistance : IsCompleteDistance (inducedDistance cigarField) :=
  completeDistance_of_compact_sublevels cigarField cigar_metricSmooth
    cigarExhaustion cigar_exhaustion_sublevel_compact cigar_exhaustion_distance

end Yau.Witness.Cigar
