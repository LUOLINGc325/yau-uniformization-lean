import Yau.LeafProofs.L19HeatGaussianTail
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Davies--Gaffney bounds for genuine L² pairings and ball indicators. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Relocating the indicator to the evolved input gives the bilinear
Davies--Gaffney bound without any kernel or mass assumption. -/
theorem scalarHeatFamily_double_support (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (r R t A : ℝ) (f k : Lp ℝ 2 μ)
    (hk : ∀ᵐ x ∂μ, x ∈ distBall g.form o R → k x = 0)
    (htail : ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
      (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t f)‖ ≤
      Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖) :
    |⟪k, scalarHeatFamily g μ hμ t f⟫_ℝ| ≤
      Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖k‖ * ‖f‖ := by
  rw [scalarL2Indicator_inner_of_support μ (distBall g.form o R)ᶜ
    (L12Aux.measurableSet_distBall g o R).compl _ k (by simpa using hk)]
  calc
    _ ≤ ‖k‖ * ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
      (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t f)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖k‖ * (Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = _ := by ring

/-- The actual two-support Davies--Gaffney estimate. Its sole support
conditions are almost-everywhere vanishing in the indicated geometric sets. -/
theorem exists_uniform_double_support_heat_DG (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
      (o : M.Carrier) (r R t : ℝ), 0 < r → r < R → 0 < t →
      ∀ (f k : Lp ℝ 2 μ),
      (∀ᵐ z ∂μ, z ∉ distBall g.form o r → f z = 0) →
      (∀ᵐ z ∂μ, z ∈ distBall g.form o R → k z = 0) →
      |⟪k, scalarHeatFamily g μ hμ t f⟫_ℝ| ≤
        Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖k‖ * ‖f‖ := by
  obtain ⟨A, hA, hDG⟩ := exists_uniform_annular_heat_L2_tail n
  refine ⟨A, hA, ?_⟩
  intro M g μ hμ o r R t hr hrR ht f k hf hk
  exact scalarHeatFamily_double_support g μ hμ o r R t A f k hk
    (hDG M g μ hμ o r R hr hrR t ht f hf)

/-- Two inputs supported in two balls satisfy the sharp positive-gap form
of the actual annular estimate. -/
theorem exists_uniform_double_ball_heat_pairing (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
      (x y : M.Carrier) (rx ry t : ℝ), 0 < rx → 0 < ry → 0 < t →
      ∀ (f k : Lp ℝ 2 μ),
      (∀ᵐ z ∂μ, z ∉ distBall g.form x rx → f z = 0) →
      (∀ᵐ z ∂μ, z ∉ distBall g.form y ry → k z = 0) →
      |⟪k, scalarHeatFamily g μ hμ t f⟫_ℝ| ≤
        Real.exp (-(max (inducedDistance g.form x y - rx - ry) 0) ^ 2 /
          (2 * A ^ 2 * t)) * ‖k‖ * ‖f‖ := by
  obtain ⟨A, hA, hDG⟩ := exists_uniform_annular_heat_L2_tail n
  refine ⟨A, hA, ?_⟩
  intro M g μ hμ x y rx ry t hrx hry ht f k hf hk
  by_cases hgap : rx < inducedDistance g.form x y - ry
  · have hR : 0 < inducedDistance g.form x y - ry := hrx.trans hgap
    have hk' : ∀ᵐ z ∂μ, z ∈ distBall g.form x (inducedDistance g.form x y - ry) → k z = 0 := by
      filter_upwards [hk] with z hz hzx
      apply hz
      intro hzy
      have h₁ := (L12Aux.mem_distBall_iff g x z hR).mp hzx
      have h₂ := (L12Aux.mem_distBall_iff g y z hry).mp hzy
      have h₃ := g.induced_distance_triangle x z y
      rw [g.induced_distance_symm z y] at h₃
      linarith
    have hd := scalarHeatFamily_double_support g μ hμ x rx
      (inducedDistance g.form x y - ry) t A f k hk'
      (hDG M g μ hμ x rx _ hrx hgap t ht f hf)
    rw [max_eq_left (by linarith : 0 ≤ inducedDistance g.form x y - rx - ry)]
    convert hd using 2 <;> congr 2 <;> ring
  · have hmax : max (inducedDistance g.form x y - rx - ry) 0 = 0 :=
      max_eq_right (by linarith)
    rw [hmax]
    simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, one_mul]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (scalarHeatFamily_norm_le g μ hμ t f) (norm_nonneg _))

/-- Native actual L² characteristic function of an original positive ball. -/
def scalarBallL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (r : ℝ) (hr : 0 < r) : Lp ℝ 2 μ :=
  indicatorConstLp 2 (L12Aux.measurableSet_distBall g x r)
    (riemannianVolume_distBall_lt_top g μ hμ x hr).ne (1 : ℝ)

theorem scalarBallL2_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (r : ℝ) (hr : 0 < r) :
    scalarBallL2 g μ hμ x r hr =ᵐ[μ] (distBall g.form x r).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

theorem scalarBallL2_norm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (r : ℝ) (hr : 0 < r) :
    ‖scalarBallL2 g μ hμ x r hr‖ = Real.sqrt (μ (distBall g.form x r)).toReal := by
  rw [scalarBallL2, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [Real.norm_eq_abs, abs_one, ENNReal.toReal_ofNat, one_mul]
  exact (Real.sqrt_eq_rpow _).symm

/-- The two-ball estimate includes the actual square root volume factors.
The dimensional constant precedes the manifold, metric, measure and balls. -/
theorem exists_uniform_double_ball_heat_DG (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
      (x y : M.Carrier) (rx ry t : ℝ) (hrx : 0 < rx) (hry : 0 < ry), 0 < t →
      |⟪scalarBallL2 g μ hμ y ry hry,
        scalarHeatFamily g μ hμ t (scalarBallL2 g μ hμ x rx hrx)⟫_ℝ| ≤
        Real.exp (-(max (inducedDistance g.form x y - rx - ry) 0) ^ 2 /
          (2 * A ^ 2 * t)) *
          Real.sqrt ((μ (distBall g.form x rx)).toReal * (μ (distBall g.form y ry)).toReal) := by
  obtain ⟨A, hA, hDG⟩ := exists_uniform_double_ball_heat_pairing n
  refine ⟨A, hA, ?_⟩
  intro M g μ hμ x y rx ry t hrx hry ht
  have hf : ∀ᵐ z ∂μ, z ∉ distBall g.form x rx → scalarBallL2 g μ hμ x rx hrx z = 0 := by
    filter_upwards [scalarBallL2_coe g μ hμ x rx hrx] with z hz hzx
    exact hz.trans (Set.indicator_of_notMem hzx _)
  have hk : ∀ᵐ z ∂μ, z ∉ distBall g.form y ry → scalarBallL2 g μ hμ y ry hry z = 0 := by
    filter_upwards [scalarBallL2_coe g μ hμ y ry hry] with z hz hzy
    exact hz.trans (Set.indicator_of_notMem hzy _)
  have hd := hDG M g μ hμ x y rx ry t hrx hry ht _ _ hf hk
  rw [scalarBallL2_norm, scalarBallL2_norm] at hd
  convert hd using 1
  rw [Real.sqrt_mul ENNReal.toReal_nonneg]
  ring

end Yau.LeafProofs.L19Aux
