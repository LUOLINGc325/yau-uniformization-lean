import Yau.Proofs.P03Measure

open scoped ENNReal Topology ContDiff
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- An explicit radial bump; radiality follows from the formula and is never
inferred from an arbitrary choice of a smooth bump base. -/
def radialBump (r : ℝ) (x : ComplexVector n) : ℝ :=
  Real.smoothTransition (1 - ‖x‖ ^ 2 / r ^ 2)

theorem radialBump_contDiff (r : ℝ) : ContDiff ℝ ∞ (radialBump (n := n) r) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℂ).div_const (r ^ 2)))

theorem radialBump_nonneg (r : ℝ) (x : ComplexVector n) : 0 ≤ radialBump r x :=
  Real.smoothTransition.nonneg _

theorem radialBump_zero (r : ℝ) : radialBump (n := n) r 0 = 1 := by
  simp [radialBump, Real.smoothTransition.one]

theorem radialBump_eq_zero_of_le_norm {r : ℝ} (hr : 0 < r)
    {x : ComplexVector n} (hx : r ≤ ‖x‖) : radialBump r x = 0 := by
  have hsq : r ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ hr.le (norm_nonneg x)).mpr hx
  have hdiv : 1 ≤ ‖x‖ ^ 2 / r ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa using hsq)
  exact Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hdiv)

theorem radialBump_tsupport_subset {r : ℝ} (hr : 0 < r) :
    tsupport (radialBump (n := n) r) ⊆ Metric.closedBall 0 r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hle : ‖x‖ ≤ r := by
    by_contra h
    exact hx (radialBump_eq_zero_of_le_norm hr (le_of_lt (lt_of_not_ge h)))
  simpa only [Metric.mem_closedBall, dist_zero_right] using hle

theorem radialBump_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (radialBump (n := n) r) :=
  (isCompact_closedBall (0 : ComplexVector n) r).of_isClosed_subset
    (isClosed_tsupport _) (radialBump_tsupport_subset hr)

theorem radialBump_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (radialBump (n := n) r) volume :=
  (radialBump_contDiff r).continuous.integrable_of_hasCompactSupport
    (radialBump_hasCompactSupport hr)

theorem radialBump_integral_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ x : ComplexVector n, radialBump r x := by
  exact integral_pos_of_integrable_nonneg_nonzero (x := (0 : ComplexVector n))
    (radialBump_contDiff r).continuous (radialBump_integrable hr)
    (radialBump_nonneg r) (by simp [radialBump_zero])

theorem radialBump_rotation (r : ℝ) (c : ℂ) (hc : ‖c‖ = 1) (x : ComplexVector n) :
    radialBump r (c • x) = radialBump r x := by
  simp only [radialBump, norm_smul, hc, one_mul]

def radialKernel (r : ℝ) (x : ComplexVector n) : ℝ :=
  radialBump r x / (∫ y : ComplexVector n, radialBump r y)

theorem radialKernel_contDiff (r : ℝ) : ContDiff ℝ ∞ (radialKernel (n := n) r) :=
  (radialBump_contDiff r).div_const _

theorem radialKernel_tsupport_subset {r : ℝ} (hr : 0 < r) :
    tsupport (radialKernel (n := n) r) ⊆ Metric.closedBall 0 r := by
  apply Set.Subset.trans _ (radialBump_tsupport_subset hr)
  apply closure_mono
  intro x hx
  by_contra hz
  have hb : radialBump r x = 0 := by simpa only [Function.mem_support, not_not] using hz
  exact hx (by simp [radialKernel, hb])

theorem radialKernel_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (radialKernel (n := n) r) :=
  (isCompact_closedBall (0 : ComplexVector n) r).of_isClosed_subset
    (isClosed_tsupport _) (radialKernel_tsupport_subset hr)

theorem radialKernel_nonneg {r : ℝ} (hr : 0 < r) (x : ComplexVector n) :
    0 ≤ radialKernel r x :=
  div_nonneg (radialBump_nonneg r x) (radialBump_integral_pos hr).le

theorem radialKernel_integral {r : ℝ} (hr : 0 < r) :
    (∫ x : ComplexVector n, radialKernel r x) = 1 := by
  simp only [radialKernel, integral_div]
  exact div_self (ne_of_gt (radialBump_integral_pos hr))

theorem radialKernel_rotation (r : ℝ) (c : ℂ) (hc : ‖c‖ = 1) (x : ComplexVector n) :
    radialKernel r (c • x) = radialKernel r x := by
  simp only [radialKernel, radialBump_rotation r c hc x]

end Yau.NodeProofs.P03Aux
