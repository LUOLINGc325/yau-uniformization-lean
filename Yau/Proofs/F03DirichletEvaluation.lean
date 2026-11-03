import Yau.Proofs.F03DirichletPointBound
import Yau.Proofs.F03DirichletClassicalSemigroup

/-! Genuine bounded evaluation and its actual Riesz vector, before all sources. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Actual point evaluation is bounded by the internally proved compact
closed-graph estimate, rather than supplied as a hypothesis. -/
def dirichletHeatEvaluation (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier) (hx : x ∈ Ω)
    (t : ℝ) (ht : 0 < t) : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] ℝ :=
  let T : Lp ℝ 2 (μ.restrict Ω) →ₗ[ℝ] ℝ :=
    { toFun := fun f => dirichletClassicalHeat g hK μ hμ Ω hΩ f x t
      map_add' := fun f k => dirichletClassicalHeat_add g hK μ hμ Ω hΩ f k ht x hx
      map_smul' := fun c f => dirichletClassicalHeat_smul g hK μ hμ Ω hΩ c f ht x hx }
  let hc := dirichletClassicalHeat_point_bound g hK μ hμ Ω hΩ x hx ht
  T.mkContinuous hc.choose (by
    intro f
    exact hc.choose_spec.2 f)

@[simp] theorem dirichletHeatEvaluation_apply (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier) (hx : x ∈ Ω)
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict Ω)) :
    dirichletHeatEvaluation g hK μ hμ Ω hΩ x hx t ht f =
      dirichletClassicalHeat g hK μ hμ Ω hΩ f x t := rfl

/-- One actual Riesz vector is determined for each positive interior point,
without any source input. -/
def dirichletHeatEvaluationVector (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier) (hx : x ∈ Ω)
    (t : ℝ) (ht : 0 < t) : Lp ℝ 2 (μ.restrict Ω) :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 (μ.restrict Ω))).symm
    (dirichletHeatEvaluation g hK μ hμ Ω hΩ x hx t ht)

@[simp] theorem dirichletHeatEvaluationVector_inner (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier) (hx : x ∈ Ω)
    (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict Ω)) :
    inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht) f =
      dirichletClassicalHeat g hK μ hμ Ω hΩ f x t := by
  simp only [dirichletHeatEvaluationVector,InnerProductSpace.toDual_symm_apply,
    dirichletHeatEvaluation_apply]

/-- The actual Riesz vectors obey the supported heat semigroup identity,
by the proved pointwise semigroup law and self-adjointness. -/
theorem dirichletHeatEvaluationVector_semigroup (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier) (hx : x ∈ Ω)
    {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t+s) (add_pos_of_pos_of_nonneg ht hs) =
      dirichletHeat g μ hμ Ω s (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht) := by
  apply ext_inner_right ℝ
  intro f
  rw [dirichletHeatEvaluationVector_inner]
  calc
    _ = dirichletClassicalHeat g hK μ hμ Ω hΩ (dirichletHeat g μ hμ Ω s f) x t :=
      dirichletClassicalHeat_semigroup g hK μ hμ Ω hΩ f ht hs x hx
    _ = inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht)
        (dirichletHeat g μ hμ Ω s f) := (dirichletHeatEvaluationVector_inner g hK μ hμ Ω hΩ x hx t ht _).symm
    _ = inner ℝ (dirichletHeat g μ hμ Ω s
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht)) f := by
      simpa only [dirichletHeat_adjoint] using
        (ContinuousLinearMap.adjoint_inner_right (dirichletHeat g μ hμ Ω s)
          (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht) f)

end Yau.Proofs.F03Aux
