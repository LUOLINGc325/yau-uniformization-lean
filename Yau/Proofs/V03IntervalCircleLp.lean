import Yau.Proofs.V03DirichletOperator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! The actual interval trace maps boundedly into normalized circle L²
using the native measurable fundamental-domain representative. Endpoint
agreement is unnecessary for this operator; periodic actual traces agree
pointwise with their original circle lift. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev BoundaryAngleInterval := Set.Icc (0 : ℝ) (2 * Real.pi)

def circleIntervalRepresentative (x : AddCircle (2 * Real.pi)) : BoundaryAngleInterval :=
  ⟨(equivIoc (2 * Real.pi) 0 x : ℝ),
    ⟨(equivIoc (2 * Real.pi) 0 x).2.1.le, by
      simpa only [zero_add] using (equivIoc (2 * Real.pi) 0 x).2.2⟩⟩

theorem measurable_circleIntervalRepresentative : Measurable circleIntervalRepresentative := by
  have hh : Measurable (fun x : AddCircle (2 * Real.pi) =>
      (equivIoc (2 * Real.pi) 0 x : ℝ)) :=
    measurable_subtype_coe.comp (measurableEquivIoc (2 * Real.pi) 0).measurable
  unfold circleIntervalRepresentative
  exact hh.subtype_mk

theorem coe_circleIntervalRepresentative (x : AddCircle (2 * Real.pi)) :
    ((circleIntervalRepresentative x : ℝ) : AddCircle (2 * Real.pi)) = x :=
  coe_equivIoc

theorem intervalTrace_memLp (f : C(BoundaryAngleInterval, ℂ)) :
    MemLp (fun x : AddCircle (2 * Real.pi) => f (circleIntervalRepresentative x)) 2 haarAddCircle :=
  MemLp.of_bound (f.continuous.measurable.comp measurable_circleIntervalRepresentative).aestronglyMeasurable
    ‖f‖ (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm _))

def intervalTraceLp (f : C(BoundaryAngleInterval, ℂ)) :
    Lp ℂ 2 (haarAddCircle (T := 2 * Real.pi)) :=
  (intervalTrace_memLp f).toLp (fun x => f (circleIntervalRepresentative x))

theorem intervalTraceLp_add (f g : C(BoundaryAngleInterval, ℂ)) :
    intervalTraceLp (f + g) = intervalTraceLp f + intervalTraceLp g := by
  exact (intervalTrace_memLp f).toLp_add (intervalTrace_memLp g)

theorem intervalTraceLp_smul (c : ℂ) (f : C(BoundaryAngleInterval, ℂ)) :
    intervalTraceLp (c • f) = c • intervalTraceLp f := by
  exact (intervalTrace_memLp f).toLp_const_smul c

theorem intervalTraceLp_norm_le (f : C(BoundaryAngleInterval, ℂ)) : ‖intervalTraceLp f‖ ≤ ‖f‖ := by
  have hb : ∀ᵐ x ∂(haarAddCircle (T := 2 * Real.pi)), ‖intervalTraceLp f x‖ ≤ ‖f‖ := by
    filter_upwards [(intervalTrace_memLp f).coeFn_toLp] with x hx
    unfold intervalTraceLp
    rw [hx]
    exact f.norm_coe_le_norm _
  have hn := Lp.norm_le_of_ae_bound (norm_nonneg f) hb
  simpa [measureUnivNNReal] using hn

def intervalCircleLpL : C(BoundaryAngleInterval, ℂ) →L[ℂ]
    Lp ℂ 2 (haarAddCircle (T := 2 * Real.pi)) :=
  LinearMap.mkContinuous
    { toFun := intervalTraceLp
      map_add' := intervalTraceLp_add
      map_smul' := intervalTraceLp_smul }
    1 (by
      intro f
      change ‖intervalTraceLp f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using intervalTraceLp_norm_le f)

theorem intervalCircleLpL_apply (f : C(BoundaryAngleInterval, ℂ)) :
    intervalCircleLpL f = intervalTraceLp f := rfl

end Yau.Blueprint.V03Proof
