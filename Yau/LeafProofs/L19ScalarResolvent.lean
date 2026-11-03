import Yau.LeafProofs.L19ScalarEnergyCompletion

/-! Resolvents constructed on the actual scalar energy completion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The closed extension of the genuine scalar energy. -/
def scalarClosedEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k : ScalarEnergySpace g μ hμ) : ℝ :=
  ⟪f, k⟫_ℝ - ⟪scalarEnergyL2 g μ hμ f, scalarEnergyL2 g μ hμ k⟫_ℝ

theorem scalarClosedEnergy_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k : ScalarEnergyDomain g μ hμ) :
    scalarClosedEnergy g μ hμ (f : ScalarEnergySpace g μ hμ) (k : ScalarEnergySpace g μ hμ) =
      scalarEnergyPair g μ f k := by
  unfold scalarClosedEnergy
  rw [UniformSpace.Completion.inner_coe, scalarEnergyDomain_inner,
    scalarEnergyL2_coe, scalarEnergyL2_coe, scalarEnergyDomainL2_inner]
  unfold scalarSobolevPair
  ring

theorem scalarClosedEnergy_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : ScalarEnergySpace g μ hμ) :
    0 ≤ scalarClosedEnergy g μ hμ f f := by
  unfold scalarClosedEnergy
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hh := scalarEnergyL2_norm_le g μ hμ f
  nlinarith [norm_nonneg f, norm_nonneg (scalarEnergyL2 g μ hμ f)]

theorem scalarClosedEnergy_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f k : ScalarEnergySpace g μ hμ) :
    scalarClosedEnergy g μ hμ f k = scalarClosedEnergy g μ hμ k f := by
  unfold scalarClosedEnergy
  rw [real_inner_comm f k, real_inner_comm (scalarEnergyL2 g μ hμ f)]

/-- The actual bounded form whose inverse yields the scalar heat
resolvent at the prescribed positive time step. -/
def scalarResolventForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) :
    ScalarEnergySpace g μ hμ →L[ℝ] ScalarEnergySpace g μ hμ →L[ℝ] ℝ :=
  (innerSL ℝ).comp (h • ContinuousLinearMap.id ℝ (ScalarEnergySpace g μ hμ) +
    (1 - h) • ((scalarEnergyL2 g μ hμ).adjoint.comp (scalarEnergyL2 g μ hμ)))

theorem scalarResolventForm_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (f k : ScalarEnergySpace g μ hμ) :
    scalarResolventForm g μ hμ h f k =
      ⟪scalarEnergyL2 g μ hμ f, scalarEnergyL2 g μ hμ k⟫_ℝ + h * scalarClosedEnergy g μ hμ f k := by
  simp only [scalarResolventForm, ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    inner_add_left, inner_smul_left, conj_trivial,
    ContinuousLinearMap.adjoint_inner_left, scalarClosedEnergy]
  ring

theorem scalarResolventForm_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (f k : ScalarEnergySpace g μ hμ) :
    scalarResolventForm g μ hμ h f k = scalarResolventForm g μ hμ h k f := by
  rw [scalarResolventForm_apply, scalarResolventForm_apply,
    scalarClosedEnergy_symm g μ hμ f k, real_inner_comm (scalarEnergyL2 g μ hμ f)]

theorem scalarResolventForm_lower_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (f : ScalarEnergySpace g μ hμ) :
    min 1 h * ‖f‖ * ‖f‖ ≤ scalarResolventForm g μ hμ h f f := by
  rw [scalarResolventForm_apply]
  have hE := scalarClosedEnergy_nonneg g μ hμ f
  have hsum : ‖f‖ ^ 2 =
      ⟪scalarEnergyL2 g μ hμ f, scalarEnergyL2 g μ hμ f⟫_ℝ + scalarClosedEnergy g μ hμ f f := by
    unfold scalarClosedEnergy
    rw [real_inner_self_eq_norm_sq f]
    ring
  have hL : 0 ≤ ⟪scalarEnergyL2 g μ hμ f, scalarEnergyL2 g μ hμ f⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) h) hL
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) h) hE
  calc
    min 1 h * ‖f‖ * ‖f‖ = min 1 h *
        (⟪scalarEnergyL2 g μ hμ f, scalarEnergyL2 g μ hμ f⟫_ℝ + scalarClosedEnergy g μ hμ f f) := by
      rw [← hsum]
      ring
    _ ≤ _ := by linarith only [h1, h2]

theorem scalarResolventForm_coercive (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {h : ℝ} (hh : 0 < h) :
    IsCoercive (scalarResolventForm g μ hμ h) :=
  ⟨min 1 h, lt_min zero_lt_one hh, scalarResolventForm_lower_bound g μ hμ h⟩

/-- This is the actual variational scalar resolvent in the fixed energy
completion, constructed by Lax--Milgram rather than supplied as data. -/
def scalarResolventEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) :
    Lp ℝ 2 μ →L[ℝ] ScalarEnergySpace g μ hμ :=
  (scalarResolventForm_coercive g μ hμ hh).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (scalarEnergyL2 g μ hμ).adjoint

def scalarResolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (scalarEnergyL2 g μ hμ).comp (scalarResolventEnergy g μ hμ h hh)

theorem scalarResolventEnergy_equation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 μ) (v : ScalarEnergySpace g μ hμ) :
    ⟪scalarResolvent g μ hμ h hh f, scalarEnergyL2 g μ hμ v⟫_ℝ +
      h * scalarClosedEnergy g μ hμ (scalarResolventEnergy g μ hμ h hh f) v =
        ⟪f, scalarEnergyL2 g μ hμ v⟫_ℝ := by
  have heq := (scalarResolventForm_coercive g μ hμ hh).continuousLinearEquivOfBilin_apply
    (scalarResolventEnergy g μ hμ h hh f) v
  have hleft : (scalarResolventForm_coercive g μ hμ hh).continuousLinearEquivOfBilin
      (scalarResolventEnergy g μ hμ h hh f) = (scalarEnergyL2 g μ hμ).adjoint f := by
    exact (scalarResolventForm_coercive g μ hμ hh).continuousLinearEquivOfBilin.apply_symm_apply _
  rw [hleft, ContinuousLinearMap.adjoint_inner_left, scalarResolventForm_apply] at heq
  exact heq.symm

theorem scalarResolvent_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 μ) :
    ‖scalarResolvent g μ hμ h hh f‖ ≤ ‖f‖ := by
  have hvar := scalarResolventEnergy_equation g μ hμ h hh f (scalarResolventEnergy g μ hμ h hh f)
  have hE := scalarClosedEnergy_nonneg g μ hμ (scalarResolventEnergy g μ hμ h hh f)
  change ⟪scalarResolvent g μ hμ h hh f, scalarResolvent g μ hμ h hh f⟫_ℝ +
    h * scalarClosedEnergy g μ hμ (scalarResolventEnergy g μ hμ h hh f)
      (scalarResolventEnergy g μ hμ h hh f) =
        ⟪f, scalarResolvent g μ hμ h hh f⟫_ℝ at hvar
  rw [real_inner_self_eq_norm_sq] at hvar
  have hCS := real_inner_le_norm f (scalarResolvent g μ hμ h hh f)
  nlinarith [mul_nonneg hh.le hE, norm_nonneg f, norm_nonneg (scalarResolvent g μ hμ h hh f)]

theorem scalarResolventEnergy_unique (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 μ) (u : ScalarEnergySpace g μ hμ)
    (hu : ∀ v : ScalarEnergySpace g μ hμ,
      ⟪scalarEnergyL2 g μ hμ u, scalarEnergyL2 g μ hμ v⟫_ℝ +
        h * scalarClosedEnergy g μ hμ u v = ⟪f, scalarEnergyL2 g μ hμ v⟫_ℝ) :
    u = scalarResolventEnergy g μ hμ h hh f := by
  apply (scalarResolventForm_coercive g μ hμ hh).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [(scalarResolventForm_coercive g μ hμ hh).continuousLinearEquivOfBilin_apply,
    (scalarResolventForm_coercive g μ hμ hh).continuousLinearEquivOfBilin_apply,
    scalarResolventForm_apply, scalarResolventForm_apply]
  exact (hu v).trans (scalarResolventEnergy_equation g μ hμ h hh f v).symm

theorem scalarResolventEnergy_one (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    scalarResolventEnergy g μ hμ 1 zero_lt_one f = (scalarEnergyL2 g μ hμ).adjoint f := by
  apply ext_inner_right ℝ
  intro v
  have hh := scalarResolventEnergy_equation g μ hμ 1 zero_lt_one f v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪scalarEnergyL2 g μ hμ (scalarResolventEnergy g μ hμ 1 zero_lt_one f),
    scalarEnergyL2 g μ hμ v⟫_ℝ + 1 * scalarClosedEnergy g μ hμ
      (scalarResolventEnergy g μ hμ 1 zero_lt_one f) v = _ at hh
  unfold scalarClosedEnergy at hh
  linarith only [hh]

theorem scalarResolvent_one_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    scalarResolvent g μ hμ 1 zero_lt_one =
      (scalarEnergyL2 g μ hμ).comp (scalarEnergyL2 g μ hμ).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  change scalarEnergyL2 g μ hμ (scalarResolventEnergy g μ hμ 1 zero_lt_one f) = _
  rw [scalarResolventEnergy_one]
  rfl

theorem scalarResolvent_one_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    (scalarResolvent g μ hμ 1 zero_lt_one).adjoint = scalarResolvent g μ hμ 1 zero_lt_one := by
  rw [scalarResolvent_one_eq, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem scalarResolvent_one_inner_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    0 ≤ ⟪scalarResolvent g μ hμ 1 zero_lt_one f, f⟫_ℝ := by
  rw [scalarResolvent_one_eq]
  change 0 ≤ ⟪scalarEnergyL2 g μ hμ ((scalarEnergyL2 g μ hμ).adjoint f), f⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_self_nonneg

/-- The actual variational objective, including its fixed scalar L²
distance term and genuine closed scalar energy. -/
def scalarResolventObjective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (f : Lp ℝ 2 μ)
    (v : ScalarEnergySpace g μ hμ) : ℝ :=
  ‖scalarEnergyL2 g μ hμ v - f‖ ^ 2 + h * scalarClosedEnergy g μ hμ v v

theorem scalarResolventObjective_eq_form (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (f : Lp ℝ 2 μ)
    (v : ScalarEnergySpace g μ hμ) :
    scalarResolventObjective g μ hμ h f v = scalarResolventForm g μ hμ h v v -
      2 * ⟪f, scalarEnergyL2 g μ hμ v⟫_ℝ + ‖f‖ ^ 2 := by
  unfold scalarResolventObjective
  rw [scalarResolventForm_apply, norm_sub_sq_real, real_inner_self_eq_norm_sq,
    real_inner_comm (scalarEnergyL2 g μ hμ v) f]
  ring

theorem scalarResolventObjective_difference (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 μ)
    (v : ScalarEnergySpace g μ hμ) :
    scalarResolventObjective g μ hμ h f v -
        scalarResolventObjective g μ hμ h f (scalarResolventEnergy g μ hμ h hh f) =
      scalarResolventForm g μ hμ h (v - scalarResolventEnergy g μ hμ h hh f)
        (v - scalarResolventEnergy g μ hμ h hh f) := by
  let u := scalarResolventEnergy g μ hμ h hh f
  have hvar (w : ScalarEnergySpace g μ hμ) :
      scalarResolventForm g μ hμ h u w = ⟪f, scalarEnergyL2 g μ hμ w⟫_ℝ := by
    rw [scalarResolventForm_apply]
    exact scalarResolventEnergy_equation g μ hμ h hh f w
  have hsub : scalarResolventForm g μ hμ h (v - u) (v - u) =
      scalarResolventForm g μ hμ h v v - scalarResolventForm g μ hμ h v u -
        scalarResolventForm g μ hμ h u v + scalarResolventForm g μ hμ h u u := by
    simp only [map_sub, sub_apply]
    ring
  rw [scalarResolventObjective_eq_form, scalarResolventObjective_eq_form]
  change _ = scalarResolventForm g μ hμ h (v - u) (v - u)
  rw [hsub, scalarResolventForm_symm g μ hμ h v u, hvar v, hvar u]
  ring

/-- The constructed resolvent is the unique strict minimizer, with an
explicit positive H¹ error term.  This is the variational input needed
to transfer actual normal contractions to the Markov bound. -/
theorem scalarResolventObjective_strict_minimum (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) (f : Lp ℝ 2 μ)
    (v : ScalarEnergySpace g μ hμ) :
    scalarResolventObjective g μ hμ h f (scalarResolventEnergy g μ hμ h hh f) +
      min 1 h * ‖v - scalarResolventEnergy g μ hμ h hh f‖ ^ 2 ≤
        scalarResolventObjective g μ hμ h f v := by
  have hcoerce : min 1 h * ‖v - scalarResolventEnergy g μ hμ h hh f‖ ^ 2 ≤
      scalarResolventForm g μ hμ h (v - scalarResolventEnergy g μ hμ h hh f)
        (v - scalarResolventEnergy g μ hμ h hh f) := by
    have hnorm : min 1 h * ‖v - scalarResolventEnergy g μ hμ h hh f‖ *
        ‖v - scalarResolventEnergy g μ hμ h hh f‖ ≤
        scalarResolventForm g μ hμ h (v - scalarResolventEnergy g μ hμ h hh f)
          (v - scalarResolventEnergy g μ hμ h hh f) := by
      exact scalarResolventForm_lower_bound g μ hμ h _
    nlinarith only [hnorm]
  rw [← scalarResolventObjective_difference g μ hμ h hh f v] at hcoerce
  linarith only [hcoerce]

end Yau.LeafProofs.L19Aux
