import Yau.LeafProofs.L19HeatWeightedEnergyMultiplier

/-! The exact weighted scalar energy identity and its closed-form extension. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem scalarGradientPair_multiplier_identity (h : HermitianField M)
    {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f) (x : M.Carrier) :
    scalarGradientPair h f (fun y => a y * (a y * f y)) x =
      scalarGradientPair h (fun y => a y * f y) (fun y => a y * f y) x -
        f x ^ 2 * scalarGradientPair h a a x := by
  rw [scalarGradientPair_mul_right h f ha (smoothFn_mul ha hf),
    scalarGradientPair_mul_right h f ha hf,
    scalarGradientPair_mul_left h ha hf,
    scalarGradientPair_mul_right h a ha hf,
    scalarGradientPair_mul_right h f ha hf,
    scalarGradientPair_symm h a f]
  ring

theorem scalarEnergyPair_multiplier_identity (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f)
    (hcf : HasCompactSupport f) :
    scalarEnergyPair g μ f (fun y => a y * (a y * f y)) =
      scalarEnergyPair g μ (fun y => a y * f y) (fun y => a y * f y) -
        (1 / 2 : ℝ) * ∫ x, f x ^ 2 * scalarGradientPair g.form a a x ∂μ := by
  have hcf2 : HasCompactSupport (fun x => f x ^ 2) := by
    have hh : HasCompactSupport (fun x => f x * f x) := hcf.mul_right
    simpa only [pow_two] using hh
  have hI := scalarGradientPair_integrable g μ hμ (smoothFn_mul ha hf)
    (smoothFn_mul ha hf) hcf.mul_left
  have hJ : Integrable (fun x => f x ^ 2 * scalarGradientPair g.form a a x) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hf 2) (smoothFn_scalarGradientPair g ha ha))
      hcf2.mul_right
  unfold scalarEnergyPair
  simp_rw [scalarGradientPair_multiplier_identity g.form ha hf]
  rw [integral_sub hI hJ]
  ring

theorem scalarEnergyPair_multiplier_lower (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f)
    (hcf : HasCompactSupport f) (ell : ℝ)
    (hrel : ∀ x, scalarGradientPair g.form a a x ≤ ell ^ 2 * a x ^ 2) :
    -(ell ^ 2 / 2) * (∫ x, (a x * f x) * (a x * f x) ∂μ) ≤
      scalarEnergyPair g μ f (fun y => a y * (a y * f y)) := by
  have hcf2 : HasCompactSupport (fun x => f x ^ 2) := by
    have hh : HasCompactSupport (fun x => f x * f x) := hcf.mul_right
    simpa only [pow_two] using hh
  have hJ : Integrable (fun x => f x ^ 2 * scalarGradientPair g.form a a x) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_pow hf 2) (smoothFn_scalarGradientPair g ha ha))
      hcf2.mul_right
  have hI : Integrable (fun x => (a x * f x) * (a x * f x)) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_mul ha hf) (smoothFn_mul ha hf))
      (hcf.mul_left.mul_right)
  have hb : (∫ x, f x ^ 2 * scalarGradientPair g.form a a x ∂μ) ≤
      ell ^ 2 * ∫ x, (a x * f x) * (a x * f x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hJ (hI.const_mul _)
    intro x
    nlinarith [mul_le_mul_of_nonneg_left (hrel x) (sq_nonneg (f x))]
  rw [scalarEnergyPair_multiplier_identity g μ hμ ha hf hcf]
  have hn := scalarEnergyPair_nonneg g μ (fun y => a y * f y)
  linarith

/-- The weighted lower energy estimate is proved on the actual completion,
by core density and the explicitly constructed bounded multipliers. -/
theorem scalarClosedEnergy_multiplier_lower (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : M.Carrier → ℝ) (ha : SmoothFn a) (B C : ℝ)
    (hB : ∀ x, |a x| ≤ B) (hC : ∀ x, scalarGradientPair g.form a a x ≤ C ^ 2)
    (ell : ℝ) (hrel : ∀ x, scalarGradientPair g.form a a x ≤ ell ^ 2 * a x ^ 2)
    (w : ScalarEnergySpace g μ hμ) :
    -(ell ^ 2 / 2) *
        ‖scalarMultiplierL2 μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB
          (scalarEnergyL2 g μ hμ w)‖ ^ 2 ≤
      scalarClosedEnergy g μ hμ w
        (scalarEnergyMultiplier g μ hμ a ha B C hB hC
          (scalarEnergyMultiplier g μ hμ a ha B C hB hC w)) := by
  let T := scalarEnergyMultiplier g μ hμ a ha B C hB hC
  let A := scalarMultiplierL2 μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB
  change -(ell ^ 2 / 2) * ‖A (scalarEnergyL2 g μ hμ w)‖ ^ 2 ≤
    scalarClosedEnergy g μ hμ w (T (T w))
  refine UniformSpace.Completion.induction_on w (p := fun v : ScalarEnergySpace g μ hμ =>
    -(ell ^ 2 / 2) * ‖A (scalarEnergyL2 g μ hμ v)‖ ^ 2 ≤
      scalarClosedEnergy g μ hμ v (T (T v))) ?_ ?_
  · apply isClosed_le
    · fun_prop
    · unfold scalarClosedEnergy
      fun_prop
  · intro f
    have hT (k : ScalarEnergyDomain g μ hμ) :
        T (k : ScalarEnergySpace g μ hμ) =
          (scalarEnergyDomainMultiplier g μ hμ a ha k : ScalarEnergySpace g μ hμ) :=
      scalarEnergyMultiplier_coe g μ hμ a ha B C hB hC k
    have hN : ‖A (scalarEnergyL2 g μ hμ (f : ScalarEnergySpace g μ hμ))‖ ^ 2 =
        ∫ x, (a x * f x) * (a x * f x) ∂μ := by
      change ‖scalarMultiplierL2 μ a _ B hB _‖ ^ 2 = _
      rw [← scalarEnergyMultiplier_L2 g μ hμ a ha B C hB hC,
        scalarEnergyMultiplier_coe, scalarEnergyL2_coe,
        ← real_inner_self_eq_norm_sq, scalarEnergyDomainL2_inner]
      rfl
    rw [hN, hT, hT, scalarClosedEnergy_coe]
    exact scalarEnergyPair_multiplier_lower g μ hμ ha f.2.1 f.2.2 ell hrel

end Yau.LeafProofs.L19Aux
