import Yau.LeafProofs.L19Exact
import Yau.LeafProofs.L12Complete

/-! The original Gaussian bound controls the same heat kernel on a closed
space-time cylinder. All volume comparisons concern the given Riemannian measure. -/
noncomputable section
open MeasureTheory
open scoped Topology ComplexOrder
namespace Yau.LeafProofs.L24Aux
open L18Aux L19Aux L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Strict positivity uses both positivity and finiteness of the actual balls. -/
theorem sqrt_ball_volume_product_pos (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x y : M.Carrier) {r : ℝ} (hr : 0 < r) :
    0 < Real.sqrt ((μ (distBall g.form x r)).toReal *
      (μ (distBall g.form y r)).toReal) := by
  apply Real.sqrt_pos.mpr
  exact mul_pos
    (ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ x hr).ne'
      (riemannianVolume_distBall_lt_top g μ hμ x hr).ne)
    (ENNReal.toReal_pos (riemannianVolume_distBall_pos g μ hμ y hr).ne'
      (riemannianVolume_distBall_lt_top g μ hμ y hr).ne)

/-- Bishop--Gromov in real-valued form, with finite-volume conversion explicit. -/
theorem ball_volume_le_of_subset_dilate (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x z : M.Carrier) {r a k : ℝ} (ha : 0 < a) (hk : 1 ≤ k)
    (hsub : distBall g.form x r ⊆ distBall g.form z (k * a)) :
    (μ (distBall g.form x r)).toReal ≤
      k ^ (2 * n) * (μ (distBall g.form z a)).toReal := by
  have hka : a ≤ k * a := by nlinarith
  have hBG := L12Aux.bishopGromov n M g hcomplete hK hRic μ hμ z a (k * a) ha hka
  have hv := (measure_mono hsub).trans hBG
  have hvreal := ENNReal.toReal_mono
    (show ENNReal.ofReal (((k * a) / a) ^ (2 * n)) *
        μ (distBall g.form z a) ≠ ⊤ from
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (riemannianVolume_distBall_lt_top g μ hμ z ha).ne) hv
  have hratio : k * a / a = k := mul_div_cancel_right₀ k ha.ne'
  simpa only [hratio, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (by linarith : 0 ≤ k) _)] using hvreal

/-- Near times give comparable square-root radii without irrational constants. -/
theorem nearby_sqrt_radii {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Icc (t / 2) t) :
    0 < Real.sqrt s ∧ Real.sqrt s ≤ Real.sqrt t ∧
      Real.sqrt t ≤ 2 * Real.sqrt s := by
  have hspos : 0 < s := by linarith [hs.1]
  refine ⟨Real.sqrt_pos.mpr hspos, Real.sqrt_le_sqrt hs.2, ?_⟩
  have hsqS := Real.sq_sqrt hspos.le
  have hsqT := Real.sq_sqrt ht.le
  nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg s, hs.1]

/-- Nearby centers and times preserve the symmetric volume denominator. -/
theorem nearby_time_volume_denominator
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {t s : ℝ} (ht : 0 < t) (hs : s ∈ Set.Icc (t / 2) t)
    (x y z : M.Carrier) (hz : inducedDistance g.form x z ≤ Real.sqrt t) :
    Real.sqrt ((μ (distBall g.form x (Real.sqrt t))).toReal *
      (μ (distBall g.form y (Real.sqrt t))).toReal) ≤
    (8 : ℝ) ^ n * Real.sqrt
      ((μ (distBall g.form z (Real.sqrt s))).toReal *
        (μ (distBall g.form y (Real.sqrt s))).toReal) := by
  obtain ⟨ha, har, hra⟩ := nearby_sqrt_radii ht hs
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsubx : distBall g.form x (Real.sqrt t) ⊆
      distBall g.form z (4 * Real.sqrt s) := by
    intro w hw
    have hw' := (mem_distBall_iff g x w hr).mp hw
    apply (mem_distBall_iff g z w (by positivity : 0 < 4 * Real.sqrt s)).mpr
    have htri := g.induced_distance_triangle z x w
    rw [g.induced_distance_symm z x] at htri
    linarith
  have hsuby : distBall g.form y (Real.sqrt t) ⊆
      distBall g.form y (2 * Real.sqrt s) := by
    intro w hw
    exact (mem_distBall_iff g y w (by positivity : 0 < 2 * Real.sqrt s)).mpr
      (((mem_distBall_iff g y w hr).mp hw).trans_le hra)
  have hx := ball_volume_le_of_subset_dilate g hcomplete hK hRic μ hμ x z ha
    (by norm_num : (1 : ℝ) ≤ 4) hsubx
  have hy := ball_volume_le_of_subset_dilate g hcomplete hK hRic μ hμ y y ha
    (by norm_num : (1 : ℝ) ≤ 2) hsuby
  have hprod := mul_le_mul hx hy (ENNReal.toReal_nonneg)
    (by positivity : 0 ≤ (4 : ℝ) ^ (2 * n) *
      (μ (distBall g.form z (Real.sqrt s))).toReal)
  have hp : (4 : ℝ) ^ (2 * n) * (2 : ℝ) ^ (2 * n) = ((8 : ℝ) ^ n) ^ 2 := by
    rw [← mul_pow]
    norm_num
    rw [← pow_mul]
    congr 1
    omega
  have hprod' :
      (μ (distBall g.form x (Real.sqrt t))).toReal *
        (μ (distBall g.form y (Real.sqrt t))).toReal ≤
      ((8 : ℝ) ^ n) ^ 2 *
        ((μ (distBall g.form z (Real.sqrt s))).toReal *
          (μ (distBall g.form y (Real.sqrt s))).toReal) := by
    calc
      _ ≤ ((4 : ℝ) ^ (2 * n) * (μ (distBall g.form z (Real.sqrt s))).toReal) *
          ((2 : ℝ) ^ (2 * n) * (μ (distBall g.form y (Real.sqrt s))).toReal) := hprod
      _ = _ := by rw [← hp]; ring
  have h₁ := Real.sq_sqrt (mul_nonneg
    (ENNReal.toReal_nonneg (a := μ (distBall g.form x (Real.sqrt t))))
    (ENNReal.toReal_nonneg (a := μ (distBall g.form y (Real.sqrt t)))))
  have h₂ := Real.sq_sqrt (mul_nonneg
    (ENNReal.toReal_nonneg (a := μ (distBall g.form z (Real.sqrt s))))
    (ENNReal.toReal_nonneg (a := μ (distBall g.form y (Real.sqrt s)))))
  have hnon : 0 ≤ (8 : ℝ) ^ n * Real.sqrt
      ((μ (distBall g.form z (Real.sqrt s))).toReal *
        (μ (distBall g.form y (Real.sqrt s))).toReal) := by positivity
  nlinarith [Real.sqrt_nonneg
    ((μ (distBall g.form x (Real.sqrt t))).toReal *
      (μ (distBall g.form y (Real.sqrt t))).toReal)]

/-- The scalar Gaussian exponent comparison on the whole closed cylinder. -/
theorem nearby_gaussian_exponent
    {c d D t s r : ℝ} (hc : 0 ≤ c)
    (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t)
    (hr : 0 ≤ r) (hrsq : r ^ 2 = t)
    (hd : 0 ≤ d) (hD : 0 ≤ D) (htri : D ≤ r + d) :
    -c * d ^ 2 / s ≤ c - (c / 2) * D ^ 2 / t := by
  have hsq : D ^ 2 ≤ 2 * t + 2 * d ^ 2 := by
    have htriSq : D ^ 2 ≤ (r + d) ^ 2 := sq_le_sq₀ hD (by positivity) |>.mpr htri
    nlinarith [sq_nonneg (r - d)]
  have hdiv : d ^ 2 / t ≤ d ^ 2 / s :=
    div_le_div_of_nonneg_left (sq_nonneg d) hs hst
  have hbase : D ^ 2 / (2 * t) - 1 ≤ d ^ 2 / t := by
    apply (le_div_iff₀ ht).mpr
    have he : (D ^ 2 / (2 * t) - 1) * t = D ^ 2 / 2 - t := by
      field_simp
    rw [he]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left (hbase.trans hdiv) hc
  have he : c * (D ^ 2 / (2 * t) - 1) = (c / 2) * D ^ 2 / t - c := by ring
  rw [he] at hm
  have he2 : -c * d ^ 2 / s = -(c * (d ^ 2 / s)) := by ring
  rw [he2]
  linarith

/-- The explicit budget used by the local Bernstein estimate. -/
def gaussianCylinderBudget (g : SmoothMetric M) (μ : Measure M.Carrier)
    (C c t : ℝ) (x y : M.Carrier) : ℝ :=
  C * (8 : ℝ) ^ n * Real.exp c *
      Real.exp (-(c / 2) * inducedDistance g.form x y ^ 2 / t) /
    Real.sqrt ((μ (distBall g.form x (Real.sqrt t))).toReal *
      (μ (distBall g.form y (Real.sqrt t))).toReal)

theorem gaussianCylinderBudget_pos (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {C c t : ℝ} (hC : 0 < C) (ht : 0 < t) (x y : M.Carrier) :
    0 < gaussianCylinderBudget g μ C c t x y := by
  unfold gaussianCylinderBudget
  apply div_pos (by positivity)
  exact sqrt_ball_volume_product_pos g μ hμ x y (Real.sqrt_pos.mpr ht)

/-- A kernel-specific original Gaussian estimate yields the explicit closed
cylinder budget; the only heat-kernel estimate used here is the displayed bound. -/
theorem gaussian_closed_cylinder_upper_bound
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z, (ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : ℝ → M.Carrier → M.Carrier → ℝ)
    {C c : ℝ} (hC : 0 < C) (hc : 0 ≤ c)
    (hG : ∀ s, 0 < s → ∀ z y,
      H s z y ≤ C * Real.exp (-c * distFrom g.form z y ^ 2 / s) /
        Real.sqrt ((μ (distBall g.form z (Real.sqrt s))).toReal *
          (μ (distBall g.form y (Real.sqrt s))).toReal))
    {t : ℝ} (ht : 0 < t) (x y : M.Carrier) :
    ∀ z s, inducedDistance g.form x z ≤ Real.sqrt t →
      s ∈ Set.Icc (t / 2) t → H s z y ≤ gaussianCylinderBudget g μ C c t x y := by
  intro z s hz hs
  have hspos : 0 < s := by linarith [hs.1]
  have hexp := nearby_gaussian_exponent hc ht hspos hs.2 (Real.sqrt_nonneg t)
    (Real.sq_sqrt ht.le) (g.induced_distance_nonneg z y)
    (g.induced_distance_nonneg x y)
    (by linarith [g.induced_distance_triangle x z y])
  have hnum : C * Real.exp (-c * inducedDistance g.form z y ^ 2 / s) ≤
      C * Real.exp c * Real.exp (-(c / 2) * inducedDistance g.form x y ^ 2 / t) := by
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by convert hexp using 1; ring)) hC.le
  have hden := nearby_time_volume_denominator g hcomplete hK hRic μ hμ ht hs x y z hz
  have hDpos := sqrt_ball_volume_product_pos g μ hμ x y (Real.sqrt_pos.mpr ht)
  have hDlocal := sqrt_ball_volume_product_pos g μ hμ z y (Real.sqrt_pos.mpr hspos)
  have hrecip : 1 / Real.sqrt
      ((μ (distBall g.form z (Real.sqrt s))).toReal *
        (μ (distBall g.form y (Real.sqrt s))).toReal) ≤
      (8 : ℝ) ^ n / Real.sqrt
      ((μ (distBall g.form x (Real.sqrt t))).toReal *
        (μ (distBall g.form y (Real.sqrt t))).toReal) := by
    apply (div_le_div_iff₀ hDlocal hDpos).mpr
    simpa only [one_mul, mul_comm] using hden
  calc
    H s z y ≤ C * Real.exp (-c * inducedDistance g.form z y ^ 2 / s) /
        Real.sqrt ((μ (distBall g.form z (Real.sqrt s))).toReal *
          (μ (distBall g.form y (Real.sqrt s))).toReal) := hG s hspos z y
    _ ≤ (C * Real.exp c * Real.exp (-(c / 2) * inducedDistance g.form x y ^ 2 / t)) *
        ((8 : ℝ) ^ n / Real.sqrt
          ((μ (distBall g.form x (Real.sqrt t))).toReal *
            (μ (distBall g.form y (Real.sqrt t))).toReal)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hnum (by simpa only [one_div] using hrecip)
        (by positivity) (by positivity)
    _ = gaussianCylinderBudget g μ C c t x y := by unfold gaussianCylinderBudget; ring

/-- Constants are selected by dimension before the geometry and the kernel.
The Gaussian input is the internally proved original L19 theorem. -/
theorem exists_gaussian_closed_cylinder_budget (n : ℕ) (hn : 0 < n) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (M : ComplexManifold n) (g : SmoothMetric M),
      IsComplete g → IsKahler g →
      (∀ z, (ricci g.form z).PosSemidef) →
      ∀ μ, IsRiemannianVolume g.form μ →
      ∀ H, LeafCandidates.ScalarHeatKernel g.form μ H →
      ∀ t, 0 < t → ∀ x y,
        0 < gaussianCylinderBudget g μ C c t x y ∧
        ∀ z s, inducedDistance g.form x z ≤ Real.sqrt t →
          s ∈ Set.Icc (t / 2) t → H s z y ≤ gaussianCylinderBudget g μ C c t x y := by
  obtain ⟨C, c, hC, hc, hG⟩ := L19Aux.liYauGaussian n hn
  refine ⟨C, c, hC, hc, ?_⟩
  intro M g hcomplete hK hRic μ hμ H hH t ht x y
  exact ⟨gaussianCylinderBudget_pos g μ hμ hC ht x y,
    gaussian_closed_cylinder_upper_bound g hcomplete hK hRic μ hμ H hC hc.le
      (hG M g hcomplete hK hRic μ hμ H hH) ht x y⟩

/-- The final Gaussian scaling algebra. This theorem is conditional only on
an explicit local estimate for the original positive heat solution. -/
theorem heatKernelGradient_of_sqrt_scale_local_gradient
    (K : ℕ → ℝ) (hKpos : ∀ n, 0 < K n)
    (hLocal : ∀ (n : ℕ) (M : ComplexManifold n) (g : SmoothMetric M),
      IsKahler g → (∀ z, (ricci g.form z).PosSemidef) →
      ∀ u : M.Carrier → ℝ → ℝ, LeafCandidates.PositiveHeatSolution g.form u →
      ∀ (x : M.Carrier) (t A : ℝ), 0 < t → 0 < A →
      (∀ z s, inducedDistance g.form x z ≤ Real.sqrt t →
        s ∈ Set.Icc (t / 2) t → u z s ≤ A) →
      Real.sqrt (gradNormSq g.form (fun z => u z t) x) ≤
        K n * A / Real.sqrt t) :
    LeafCandidates.HeatKernelGradient := by
  intro n hn
  obtain ⟨C, c, hC, hc, hG⟩ := exists_gaussian_closed_cylinder_budget n hn
  have hKn : 0 < K n := hKpos n
  refine ⟨K n * C * (8 : ℝ) ^ n * Real.exp c, c / 2, by positivity, by positivity, ?_⟩
  intro M g hcomplete hK hRic μ hμ H hH t ht x y
  obtain ⟨hA, hbound⟩ := hG M g hcomplete hK hRic μ hμ H hH t ht x y
  have hL := hLocal n M g hK hRic (fun z s => H s z y) (hH.1 y)
    x t (gaussianCylinderBudget g μ C c t x y) ht hA hbound
  calc
    Real.sqrt (gradNormSq g.form (fun z => H t z y) x) ≤
        K n * gaussianCylinderBudget g μ C c t x y / Real.sqrt t := hL
    _ = (K n * C * (8 : ℝ) ^ n * Real.exp c) / Real.sqrt t *
        Real.exp (-(c / 2) * distFrom g.form x y ^ 2 / t) /
        Real.sqrt ((μ (distBall g.form x (Real.sqrt t))).toReal *
          (μ (distBall g.form y (Real.sqrt t))).toReal) := by
      simp only [gaussianCylinderBudget, distFrom, lengthDist]
      ring

end Yau.LeafProofs.L24Aux
