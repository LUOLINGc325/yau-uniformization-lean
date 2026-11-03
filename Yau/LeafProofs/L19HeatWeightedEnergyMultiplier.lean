import Yau.LeafProofs.L19HeatFamilyDerivative

/-! Actual bounded scalar multiplication on L² and on the energy completion. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section L2
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hB : ∀ x, |a x| ≤ B)

include ha B hB in
theorem scalarMultiplierL2Mem (f : Lp ℝ 2 μ) : MemLp (fun x => a x * f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := B) (ha.mul (Lp.aestronglyMeasurable f))
  exact ae_of_all _ (fun x => by
    change ‖a x * f x‖ ≤ B * ‖f x‖
    rw [norm_mul, Real.norm_eq_abs (a x)]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))

def scalarMultiplierL2Fn (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (scalarMultiplierL2Mem μ a ha B hB f).toLp (fun x => a x * f x)

theorem scalarMultiplierL2Fn_coe (f : Lp ℝ 2 μ) :
    scalarMultiplierL2Fn μ a ha B hB f =ᵐ[μ] (fun x => a x * f x) :=
  (scalarMultiplierL2Mem μ a ha B hB f).coeFn_toLp

def scalarMultiplierL2Linear : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := scalarMultiplierL2Fn μ a ha B hB
  map_add' f k := by
    apply Lp.ext
    filter_upwards [scalarMultiplierL2Fn_coe μ a ha B hB (f + k),
      scalarMultiplierL2Fn_coe μ a ha B hB f, scalarMultiplierL2Fn_coe μ a ha B hB k,
      Lp.coeFn_add f k, Lp.coeFn_add (scalarMultiplierL2Fn μ a ha B hB f)
        (scalarMultiplierL2Fn μ a ha B hB k)] with x hs hf hk hsum hout
    simp only [hs, hout, Pi.add_apply, hsum, hf, hk, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [scalarMultiplierL2Fn_coe μ a ha B hB (c • f),
      scalarMultiplierL2Fn_coe μ a ha B hB f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (scalarMultiplierL2Fn μ a ha B hB f)] with x hs hf hsmul hout
    simp only [RingHom.id_apply, hs, hout, Pi.smul_apply, smul_eq_mul, hsmul, hf]
    ring

theorem scalarMultiplierL2Fn_norm_le (f : Lp ℝ 2 μ) :
    ‖scalarMultiplierL2Fn μ a ha B hB f‖ ≤ B * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarMultiplierL2Fn_coe μ a ha B hB f] with x hx
  rw [hx, norm_mul, Real.norm_eq_abs (a x)]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-- Pointwise multiplication, defined on actual L² equivalence classes. -/
def scalarMultiplierL2 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (scalarMultiplierL2Linear μ a ha B hB).mkContinuous B
    (scalarMultiplierL2Fn_norm_le μ a ha B hB)

theorem scalarMultiplierL2_coe (f : Lp ℝ 2 μ) :
    scalarMultiplierL2 μ a ha B hB f =ᵐ[μ] (fun x => a x * f x) :=
  scalarMultiplierL2Fn_coe μ a ha B hB f

theorem scalarMultiplierL2_inner_square (f k : Lp ℝ 2 μ) :
    ⟪scalarMultiplierL2 μ a ha B hB f, scalarMultiplierL2 μ a ha B hB k⟫_ℝ =
      ⟪f, scalarMultiplierL2 μ a ha B hB (scalarMultiplierL2 μ a ha B hB k)⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarMultiplierL2_coe μ a ha B hB f,
    scalarMultiplierL2_coe μ a ha B hB k,
    scalarMultiplierL2_coe μ a ha B hB (scalarMultiplierL2 μ a ha B hB k)]
    with x hf hk hkk
  simp only [hf, hk, hkk, RCLike.inner_apply, conj_trivial]
  ring
end L2

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarGradientPair_mul_left (h : HermitianField M)
    {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f)
    (k : M.Carrier → ℝ) (x : M.Carrier) :
    scalarGradientPair h (fun y => a y * f y) k x =
      a x * scalarGradientPair h f k x + f x * scalarGradientPair h a k x := by
  have hp := chartGradientPair_mul_left h x (inChart x k)
    ((contDiffAt_inChart ha x (mem_extChartAt_target x)).differentiableAt (by simp))
    ((contDiffAt_inChart hf x (mem_extChartAt_target x)).differentiableAt (by simp))
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  change scalarGradientPair h (fun y => a y * f y) k x =
    a (chartInv x (chartPt x x)) * scalarGradientPair h f k x +
      f (chartInv x (chartPt x x)) * scalarGradientPair h a k x at hp
  simpa only [hx] using hp

theorem scalarGradientPair_mul_right (h : HermitianField M)
    (k : M.Carrier → ℝ) {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f)
    (x : M.Carrier) :
    scalarGradientPair h k (fun y => a y * f y) x =
      a x * scalarGradientPair h k f x + f x * scalarGradientPair h k a x := by
  rw [scalarGradientPair_symm, scalarGradientPair_mul_left h ha hf,
    scalarGradientPair_symm h f k, scalarGradientPair_symm h a k]

section Energy
variable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier → ℝ) (ha : SmoothFn a)
    (B C : ℝ) (hB : ∀ x, |a x| ≤ B)
    (hC : ∀ x, scalarGradientPair g.form a a x ≤ C ^ 2)

def scalarEnergyDomainMultiplier (f : ScalarEnergyDomain g μ hμ) :
    ScalarEnergyDomain g μ hμ :=
  ⟨fun x => a x * f x, smoothFn_mul ha f.2.1, f.2.2.mul_left⟩

def scalarEnergyDomainMultiplierLinear :
    ScalarEnergyDomain g μ hμ →ₗ[ℝ] ScalarEnergyDomain g μ hμ where
  toFun := scalarEnergyDomainMultiplier g μ hμ a ha
  map_add' f k := by apply Subtype.ext; funext x; exact mul_add _ _ _
  map_smul' c f := by apply Subtype.ext; funext x; exact mul_left_comm _ _ _

include hB hC in
theorem scalarEnergyDomainMultiplier_norm_le (f : ScalarEnergyDomain g μ hμ) :
    ‖scalarEnergyDomainMultiplier g μ hμ a ha f‖ ≤
      (2 * (1 + B ^ 2 + C ^ 2)) * ‖f‖ := by
  let v := scalarEnergyDomainMultiplier g μ hμ a ha f
  have hL := compactScalar_product_integrable g μ hμ f f
  have hE := scalarGradientPair_integrable g μ hμ f.2.1 f.2.1 f.2.2
  have hEL := scalarGradientPair_integrable g μ hμ v.2.1 v.2.1 v.2.2
  have hVL := compactScalar_product_integrable g μ hμ v v
  have hab (x : M.Carrier) : a x ^ 2 ≤ B ^ 2 := by
    have hb := hB x
    have hbn : 0 ≤ B := (abs_nonneg _).trans hb
    nlinarith [sq_abs (a x), abs_nonneg (a x)]
  have hvL : (∫ x, v x * v x ∂μ) ≤ B ^ 2 * ∫ x, f x * f x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hVL (hL.const_mul _)
    intro x
    change (a x * f x) * (a x * f x) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right (hab x) (sq_nonneg (f x))]
  have hvE : (∫ x, scalarGradientPair g.form v v x ∂μ) ≤
      2 * (B ^ 2 * ∫ x, scalarGradientPair g.form f f x ∂μ +
        C ^ 2 * ∫ x, f x * f x ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hE.const_mul _) (hL.const_mul _),
      ← integral_const_mul]
    apply integral_mono hEL (((hE.const_mul _).add (hL.const_mul _)).const_mul 2)
    intro x
    have hp := scalarGradientPair_product_self_le g.form f.2.1 ha x
    change scalarGradientPair g.form (fun x => a x * f x) (fun x => a x * f x) x ≤
      2 * (B ^ 2 * scalarGradientPair g.form f f x + C ^ 2 * (f x * f x))
    have h1 := mul_le_mul_of_nonneg_right (hab x) (scalarGradientPair_self_nonneg g.form f x)
    have h2 := mul_le_mul_of_nonneg_left (hC x) (sq_nonneg (f x))
    nlinarith
  have hfN := real_inner_self_eq_norm_sq f
  have hvN := real_inner_self_eq_norm_sq v
  rw [scalarEnergyDomain_inner] at hfN hvN
  unfold scalarSobolevPair scalarEnergyPair at hfN hvN
  have hnL : 0 ≤ ∫ x, f x * f x ∂μ := integral_nonneg (fun _ => mul_self_nonneg _)
  have hnE : 0 ≤ ∫ x, scalarGradientPair g.form f f x ∂μ :=
    integral_nonneg (scalarGradientPair_self_nonneg g.form f)
  have hsq : ‖v‖ ^ 2 ≤ (2 * (1 + B ^ 2 + C ^ 2)) * ‖f‖ ^ 2 := by
    nlinarith [sq_nonneg B, sq_nonneg C,
      mul_nonneg (sq_nonneg B) hnL, mul_nonneg (sq_nonneg C) hnE,
      mul_nonneg (sq_nonneg B) hnE]
  have hK : 1 ≤ 2 * (1 + B ^ 2 + C ^ 2) := by nlinarith [sq_nonneg B, sq_nonneg C]
  have hlarge : (2 * (1 + B ^ 2 + C ^ 2)) * ‖f‖ ^ 2 ≤
      ((2 * (1 + B ^ 2 + C ^ 2)) * ‖f‖) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (2 * (1 + B ^ 2 + C ^ 2) - 1)) (sq_nonneg ‖f‖),
      mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg ‖f‖)]
  change ‖v‖ ≤ _
  nlinarith [norm_nonneg v, norm_nonneg f,
    mul_nonneg (show 0 ≤ 2 * (1 + B ^ 2 + C ^ 2) by linarith) (norm_nonneg f)]

def scalarEnergyDomainMultiplierCLM :
    ScalarEnergyDomain g μ hμ →L[ℝ] ScalarEnergyDomain g μ hμ :=
  (scalarEnergyDomainMultiplierLinear g μ hμ a ha).mkContinuous _
    (scalarEnergyDomainMultiplier_norm_le g μ hμ a ha B C hB hC)

/-- The multiplier on H¹ is constructed from the genuine core product rule. -/
def scalarEnergyMultiplier : ScalarEnergySpace g μ hμ →L[ℝ] ScalarEnergySpace g μ hμ :=
  (UniformSpace.Completion.toComplL.comp
    (scalarEnergyDomainMultiplierCLM g μ hμ a ha B C hB hC)).extend
      UniformSpace.Completion.toComplL

theorem scalarEnergyMultiplier_coe (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergyMultiplier g μ hμ a ha B C hB hC (f : ScalarEnergySpace g μ hμ) =
      (scalarEnergyDomainMultiplier g μ hμ a ha f : ScalarEnergySpace g μ hμ) :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) f

theorem scalarEnergyMultiplier_L2 (f : ScalarEnergySpace g μ hμ) :
    scalarEnergyL2 g μ hμ (scalarEnergyMultiplier g μ hμ a ha B C hB hC f) =
      scalarMultiplierL2 μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB
        (scalarEnergyL2 g μ hμ f) := by
  refine UniformSpace.Completion.induction_on f (p := fun v : ScalarEnergySpace g μ hμ =>
    scalarEnergyL2 g μ hμ (scalarEnergyMultiplier g μ hμ a ha B C hB hC v) =
      scalarMultiplierL2 μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB
        (scalarEnergyL2 g μ hμ v)) ?_ ?_
  · exact isClosed_eq ((scalarEnergyL2 g μ hμ).continuous.comp
      (scalarEnergyMultiplier g μ hμ a ha B C hB hC).continuous)
      ((scalarMultiplierL2 μ a _ B hB).continuous.comp (scalarEnergyL2 g μ hμ).continuous)
  · intro k
    rw [scalarEnergyMultiplier_coe, scalarEnergyL2_coe, scalarEnergyL2_coe]
    apply Lp.ext
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ (scalarEnergyDomainMultiplier g μ hμ a ha k),
      scalarEnergyDomainL2_coe g μ hμ k,
      scalarMultiplierL2_coe μ a (continuous_of_smoothFn ha).aestronglyMeasurable B hB
        (scalarEnergyDomainL2 g μ hμ k)] with x hk hf hm
    rw [hk, hm, hf]
    rfl
end Energy
end Yau.LeafProofs.L19Aux
