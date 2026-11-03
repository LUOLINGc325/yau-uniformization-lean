import Yau.Proofs.F03DirichletResolventBounds

/-! Positive-step resolvents constructed on the actual supported energy space. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

theorem dirichletClosedEnergy_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : DirichletEnergy g μ hμ O) :
    0 ≤ dirichletClosedEnergy g μ hμ O f f := by
  unfold dirichletClosedEnergy
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hh := dirichletL2_norm_le g μ hμ O f
  nlinarith [norm_nonneg f, norm_nonneg (dirichletL2 g μ hμ O f)]

theorem dirichletClosedEnergy_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f k : DirichletEnergy g μ hμ O) :
    dirichletClosedEnergy g μ hμ O f k = dirichletClosedEnergy g μ hμ O k f := by
  unfold dirichletClosedEnergy
  rw [real_inner_comm f k, real_inner_comm (dirichletL2 g μ hμ O f)]

/-- The actual bounded form whose inverse yields the scalar heat
resolvent at the prescribed positive time step. -/
def dirichletStepResolventForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) :
    DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ :=
  (innerSL ℝ).comp (h • ContinuousLinearMap.id ℝ (DirichletEnergy g μ hμ O) +
    (1 - h) • ((dirichletL2 g μ hμ O).adjoint.comp (dirichletL2 g μ hμ O)))

theorem dirichletStepResolventForm_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (f k : DirichletEnergy g μ hμ O) :
    dirichletStepResolventForm g μ hμ O h f k =
      ⟪dirichletL2 g μ hμ O f, dirichletL2 g μ hμ O k⟫_ℝ + h * dirichletClosedEnergy g μ hμ O f k := by
  simp only [dirichletStepResolventForm, ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    inner_add_left, inner_smul_left, conj_trivial,
    ContinuousLinearMap.adjoint_inner_left, dirichletClosedEnergy]
  ring

theorem dirichletStepResolventForm_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (f k : DirichletEnergy g μ hμ O) :
    dirichletStepResolventForm g μ hμ O h f k = dirichletStepResolventForm g μ hμ O h k f := by
  rw [dirichletStepResolventForm_apply, dirichletStepResolventForm_apply,
    dirichletClosedEnergy_symm g μ hμ O f k, real_inner_comm (dirichletL2 g μ hμ O f)]

theorem dirichletStepResolventForm_lower_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (f : DirichletEnergy g μ hμ O) :
    min 1 h * ‖f‖ * ‖f‖ ≤ dirichletStepResolventForm g μ hμ O h f f := by
  rw [dirichletStepResolventForm_apply]
  have hE := dirichletClosedEnergy_nonneg g μ hμ O f
  have hsum : ‖f‖ ^ 2 =
      ⟪dirichletL2 g μ hμ O f, dirichletL2 g μ hμ O f⟫_ℝ + dirichletClosedEnergy g μ hμ O f f := by
    unfold dirichletClosedEnergy
    rw [real_inner_self_eq_norm_sq f]
    ring
  have hL : 0 ≤ ⟪dirichletL2 g μ hμ O f, dirichletL2 g μ hμ O f⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) h) hL
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) h) hE
  calc
    min 1 h * ‖f‖ * ‖f‖ = min 1 h *
        (⟪dirichletL2 g μ hμ O f, dirichletL2 g μ hμ O f⟫_ℝ + dirichletClosedEnergy g μ hμ O f f) := by
      rw [← hsum]
      ring
    _ ≤ _ := by linarith only [h1, h2]

theorem dirichletStepResolventForm_coercive (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {h : ℝ} (hh : 0 < h) :
    IsCoercive (dirichletStepResolventForm g μ hμ O h) :=
  ⟨min 1 h, lt_min zero_lt_one hh, dirichletStepResolventForm_lower_bound g μ hμ O h⟩

/-- This is the actual variational scalar resolvent in the fixed energy
completion, constructed by Lax--Milgram rather than supplied as data. -/
def dirichletStepResolventEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) :
    Lp ℝ 2 (μ.restrict O) →L[ℝ] DirichletEnergy g μ hμ O :=
  (dirichletStepResolventForm_coercive g μ hμ O hh).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (dirichletL2 g μ hμ O).adjoint

def dirichletStepResolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) : Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 (μ.restrict O) :=
  (dirichletL2 g μ hμ O).comp (dirichletStepResolventEnergy g μ hμ O h hh)

theorem dirichletStepResolventEnergy_equation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (μ.restrict O)) (v : DirichletEnergy g μ hμ O) :
    ⟪dirichletStepResolvent g μ hμ O h hh f, dirichletL2 g μ hμ O v⟫_ℝ +
      h * dirichletClosedEnergy g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh f) v =
        ⟪f, dirichletL2 g μ hμ O v⟫_ℝ := by
  have heq := (dirichletStepResolventForm_coercive g μ hμ O hh).continuousLinearEquivOfBilin_apply
    (dirichletStepResolventEnergy g μ hμ O h hh f) v
  have hleft : (dirichletStepResolventForm_coercive g μ hμ O hh).continuousLinearEquivOfBilin
      (dirichletStepResolventEnergy g μ hμ O h hh f) = (dirichletL2 g μ hμ O).adjoint f := by
    exact (dirichletStepResolventForm_coercive g μ hμ O hh).continuousLinearEquivOfBilin.apply_symm_apply _
  rw [hleft, ContinuousLinearMap.adjoint_inner_left, dirichletStepResolventForm_apply] at heq
  exact heq.symm

theorem dirichletStepResolvent_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 (μ.restrict O)) :
    ‖dirichletStepResolvent g μ hμ O h hh f‖ ≤ ‖f‖ := by
  have hvar := dirichletStepResolventEnergy_equation g μ hμ O h hh f (dirichletStepResolventEnergy g μ hμ O h hh f)
  have hE := dirichletClosedEnergy_nonneg g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh f)
  change ⟪dirichletStepResolvent g μ hμ O h hh f, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ +
    h * dirichletClosedEnergy g μ hμ O (dirichletStepResolventEnergy g μ hμ O h hh f)
      (dirichletStepResolventEnergy g μ hμ O h hh f) =
        ⟪f, dirichletStepResolvent g μ hμ O h hh f⟫_ℝ at hvar
  rw [real_inner_self_eq_norm_sq] at hvar
  have hCS := real_inner_le_norm f (dirichletStepResolvent g μ hμ O h hh f)
  nlinarith [mul_nonneg hh.le hE, norm_nonneg f, norm_nonneg (dirichletStepResolvent g μ hμ O h hh f)]

theorem dirichletStepResolventEnergy_unique (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (μ.restrict O)) (u : DirichletEnergy g μ hμ O)
    (hu : ∀ v : DirichletEnergy g μ hμ O,
      ⟪dirichletL2 g μ hμ O u, dirichletL2 g μ hμ O v⟫_ℝ +
        h * dirichletClosedEnergy g μ hμ O u v = ⟪f, dirichletL2 g μ hμ O v⟫_ℝ) :
    u = dirichletStepResolventEnergy g μ hμ O h hh f := by
  apply (dirichletStepResolventForm_coercive g μ hμ O hh).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [(dirichletStepResolventForm_coercive g μ hμ O hh).continuousLinearEquivOfBilin_apply,
    (dirichletStepResolventForm_coercive g μ hμ O hh).continuousLinearEquivOfBilin_apply,
    dirichletStepResolventForm_apply, dirichletStepResolventForm_apply]
  exact (hu v).trans (dirichletStepResolventEnergy_equation g μ hμ O h hh f v).symm

theorem dirichletStepResolventEnergy_one (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : Lp ℝ 2 (μ.restrict O)) :
    dirichletStepResolventEnergy g μ hμ O 1 zero_lt_one f = (dirichletL2 g μ hμ O).adjoint f := by
  apply ext_inner_right ℝ
  intro v
  have hh := dirichletStepResolventEnergy_equation g μ hμ O 1 zero_lt_one f v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪dirichletL2 g μ hμ O (dirichletStepResolventEnergy g μ hμ O 1 zero_lt_one f),
    dirichletL2 g μ hμ O v⟫_ℝ + 1 * dirichletClosedEnergy g μ hμ O
      (dirichletStepResolventEnergy g μ hμ O 1 zero_lt_one f) v = _ at hh
  unfold dirichletClosedEnergy at hh
  linarith only [hh]

theorem dirichletStepResolvent_one_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    dirichletStepResolvent g μ hμ O 1 zero_lt_one =
      (dirichletL2 g μ hμ O).comp (dirichletL2 g μ hμ O).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  change dirichletL2 g μ hμ O (dirichletStepResolventEnergy g μ hμ O 1 zero_lt_one f) = _
  rw [dirichletStepResolventEnergy_one]
  rfl

theorem dirichletStepResolvent_one_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    (dirichletStepResolvent g μ hμ O 1 zero_lt_one).adjoint = dirichletStepResolvent g μ hμ O 1 zero_lt_one := by
  rw [dirichletStepResolvent_one_eq, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem dirichletStepResolvent_one_inner_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : Lp ℝ 2 (μ.restrict O)) :
    0 ≤ ⟪dirichletStepResolvent g μ hμ O 1 zero_lt_one f, f⟫_ℝ := by
  rw [dirichletStepResolvent_one_eq]
  change 0 ≤ ⟪dirichletL2 g μ hμ O ((dirichletL2 g μ hμ O).adjoint f), f⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_self_nonneg

/-- The actual variational objective, including its fixed scalar L²
distance term and genuine closed scalar energy. -/
def dirichletStepResolventObjective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (f : Lp ℝ 2 (μ.restrict O))
    (v : DirichletEnergy g μ hμ O) : ℝ :=
  ‖dirichletL2 g μ hμ O v - f‖ ^ 2 + h * dirichletClosedEnergy g μ hμ O v v

theorem dirichletStepResolventObjective_eq_form (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (f : Lp ℝ 2 (μ.restrict O))
    (v : DirichletEnergy g μ hμ O) :
    dirichletStepResolventObjective g μ hμ O h f v = dirichletStepResolventForm g μ hμ O h v v -
      2 * ⟪f, dirichletL2 g μ hμ O v⟫_ℝ + ‖f‖ ^ 2 := by
  unfold dirichletStepResolventObjective
  rw [dirichletStepResolventForm_apply, norm_sub_sq_real, real_inner_self_eq_norm_sq,
    real_inner_comm (dirichletL2 g μ hμ O v) f]
  ring

theorem dirichletStepResolventObjective_difference (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 (μ.restrict O))
    (v : DirichletEnergy g μ hμ O) :
    dirichletStepResolventObjective g μ hμ O h f v -
        dirichletStepResolventObjective g μ hμ O h f (dirichletStepResolventEnergy g μ hμ O h hh f) =
      dirichletStepResolventForm g μ hμ O h (v - dirichletStepResolventEnergy g μ hμ O h hh f)
        (v - dirichletStepResolventEnergy g μ hμ O h hh f) := by
  let u := dirichletStepResolventEnergy g μ hμ O h hh f
  have hvar (w : DirichletEnergy g μ hμ O) :
      dirichletStepResolventForm g μ hμ O h u w = ⟪f, dirichletL2 g μ hμ O w⟫_ℝ := by
    rw [dirichletStepResolventForm_apply]
    exact dirichletStepResolventEnergy_equation g μ hμ O h hh f w
  have hsub : dirichletStepResolventForm g μ hμ O h (v - u) (v - u) =
      dirichletStepResolventForm g μ hμ O h v v - dirichletStepResolventForm g μ hμ O h v u -
        dirichletStepResolventForm g μ hμ O h u v + dirichletStepResolventForm g μ hμ O h u u := by
    simp only [map_sub, sub_apply]
    ring
  rw [dirichletStepResolventObjective_eq_form, dirichletStepResolventObjective_eq_form]
  change _ = dirichletStepResolventForm g μ hμ O h (v - u) (v - u)
  rw [hsub, dirichletStepResolventForm_symm g μ hμ O h v u, hvar v, hvar u]
  ring

/-- The constructed resolvent is the unique strict minimizer, with an
explicit positive H¹ error term.  This is the variational input needed
to transfer actual normal contractions to the Markov bound. -/
theorem dirichletStepResolventObjective_strict_minimum (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 (μ.restrict O))
    (v : DirichletEnergy g μ hμ O) :
    dirichletStepResolventObjective g μ hμ O h f (dirichletStepResolventEnergy g μ hμ O h hh f) +
      min 1 h * ‖v - dirichletStepResolventEnergy g μ hμ O h hh f‖ ^ 2 ≤
        dirichletStepResolventObjective g μ hμ O h f v := by
  have hcoerce : min 1 h * ‖v - dirichletStepResolventEnergy g μ hμ O h hh f‖ ^ 2 ≤
      dirichletStepResolventForm g μ hμ O h (v - dirichletStepResolventEnergy g μ hμ O h hh f)
        (v - dirichletStepResolventEnergy g μ hμ O h hh f) := by
    have hnorm : min 1 h * ‖v - dirichletStepResolventEnergy g μ hμ O h hh f‖ *
        ‖v - dirichletStepResolventEnergy g μ hμ O h hh f‖ ≤
        dirichletStepResolventForm g μ hμ O h (v - dirichletStepResolventEnergy g μ hμ O h hh f)
          (v - dirichletStepResolventEnergy g μ hμ O h hh f) := by
      exact dirichletStepResolventForm_lower_bound g μ hμ O h _
    nlinarith only [hnorm]
  rw [← dirichletStepResolventObjective_difference g μ hμ O h hh f v] at hcoerce
  linarith only [hcoerce]

end Yau.Proofs.F03Aux
