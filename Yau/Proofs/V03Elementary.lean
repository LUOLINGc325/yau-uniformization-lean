import Yau.Blueprint.VariationContracts

/-! Elementary facts used by the V03 proof, for the original computed walls,
clock, energy and penalized functional. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem circlePoint_norm (θ : ℝ) : ‖circlePoint θ‖ = 1 := by
  simp [circlePoint, Complex.norm_exp]

theorem circlePoint_mem_closedBall (θ : ℝ) :
    circlePoint θ ∈ Metric.closedBall (0 : ℂ) 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right, circlePoint_norm]

theorem radial_center (F : VariationDisc X) (r : ℝ) :
    (radialVariationDisc F r).f 0 = F.f 0 := by
  simp [radialVariationDisc]

theorem radial_clock_center (F : VariationDisc X) (r : ℝ) :
    (radialVariationDisc F r).w 0 = F.w 0 := by
  simp [radialVariationDisc]

theorem radial_discTime (F : VariationDisc X) (r : ℝ) (ζ : ℂ) :
    discTime (radialVariationDisc F r) ζ = discTime F ((r : ℂ) * ζ) := rfl

theorem radial_initiallyExtended (F : VariationDisc X)
    (hf : CotangentDisc F.f)
    (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    InitiallyExtendedVariationDisc (radialVariationDisc F r) := by
  refine ⟨r⁻¹, (one_lt_inv₀ hr).mpr hr1, ?_, ?_⟩
  · convert hf using 1
    funext ζ
    simp [radialVariationDisc, ← mul_assoc, ← Complex.ofReal_mul, hr.ne']
  · convert hw using 1
    funext ζ
    simp [radialVariationDisc, ← mul_assoc, ← Complex.ofReal_mul, hr.ne']

theorem discTime_pos {F : VariationDisc X} (hs : 0 < F.s) (ζ : ℂ) :
    0 < discTime F ζ :=
  mul_pos hs (Real.exp_pos _)

theorem discTime_zero {F : VariationDisc X} (hw : F.w 0 = 0) :
    discTime F 0 = F.s := by
  simp [discTime, hw]

theorem admissible_discTime_mem {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) :
    discTime F ζ ∈ Set.Ioo 0 d.T :=
  ⟨discTime_pos hF.2.2.2.1 ζ, hF.2.2.2.2.2.2.1 ζ hζ⟩

theorem deltaBase_pos {d : VariationData X q} (hp : WallProfiles d)
    {j : ℕ} (hA : 0 < d.A j) {x : Pt X} (hx : d.u x < d.A j) :
    0 < deltaBase d j x := by
  exact (hp.2.2.1 _).2.2.1.mpr ((div_lt_one hA).mpr hx)

theorem deltaFiber_pos {d : VariationData X q} (hp : WallProfiles d)
    {j : ℕ} (hB : 0 < d.B j) {y : CotangentPoint X.manifold}
    (hy : dualNorm (d.h 0) y.1 y.2 < d.B j ^ 2) :
    0 < deltaFiber d j y := by
  exact (hp.2.2.2 _).2.2.1.mpr ((div_lt_one (sq_pos_of_pos hB)).mpr hy)

theorem deltaBase_le_one {d : VariationData X q} (hp : WallProfiles d)
    (j : ℕ) (x : Pt X) : deltaBase d j x ≤ 1 :=
  (hp.2.2.1 _).2.1

theorem deltaFiber_le_one {d : VariationData X q} (hp : WallProfiles d)
    (j : ℕ) (y : CotangentPoint X.manifold) : deltaFiber d j y ≤ 1 :=
  (hp.2.2.2 _).2.1

theorem wallBase_nonneg {d : VariationData X q} (hp : WallProfiles d)
    {j : ℕ} {x : Pt X} (hx : 0 < deltaBase d j x) :
    0 ≤ wallBase d j x := by
  dsimp [wallBase]
  exact sub_nonneg.mpr ((one_le_inv₀ hx).mpr (deltaBase_le_one hp j x))

theorem wallFiber_nonneg {d : VariationData X q} (hp : WallProfiles d)
    {j : ℕ} {y : CotangentPoint X.manifold} (hy : 0 < deltaFiber d j y) :
    0 ≤ wallFiber d j y := by
  dsimp [wallFiber]
  exact sub_nonneg.mpr ((one_le_inv₀ hy).mpr (deltaFiber_le_one hp j y))

theorem variationEnergy_toReal_nonneg (d : VariationData X q) (j : ℕ)
    (F : VariationDisc X) : 0 ≤ (variationEnergy d j F).toReal :=
  ENNReal.toReal_nonneg

theorem penalizedFunctional_sub (d : VariationData X q) (j : ℕ)
    (ε ε' : ℝ) (F : VariationDisc X) :
    penalizedFunctional d j ε' F - penalizedFunctional d j ε F =
      (ε' - ε) * (variationEnergy d j F).toReal := by
  unfold penalizedFunctional
  ring

theorem penalizedFunctional_mono (d : VariationData X q) (j : ℕ)
    {ε ε' : ℝ} (hε : ε ≤ ε') (F : VariationDisc X) :
    penalizedFunctional d j ε F ≤ penalizedFunctional d j ε' F := by
  have h := mul_nonneg (sub_nonneg.mpr hε) (variationEnergy_toReal_nonneg d j F)
  rw [← penalizedFunctional_sub d j ε ε' F] at h
  exact sub_nonneg.mp h

theorem localizedInfimum_mono (d : VariationData X q) (j : ℕ) :
    Monotone (localizedInfimum d j) := by
  intro ε ε' hε
  exact iInf_mono fun F => iInf_mono fun _ =>
    EReal.coe_le_coe_iff.mpr (penalizedFunctional_mono d j hε F)

theorem localizedInfimum_le {d : VariationData X q} {j : ℕ} (ε : ℝ)
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    localizedInfimum d j ε ≤ (penalizedFunctional d j ε F : EReal) :=
  iInf₂_le F hF

theorem circleAverage_nonneg {f : ℝ → ℝ} (hf : ∀ θ, 0 ≤ f θ) :
    0 ≤ circleAverage f := by
  unfold circleAverage
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg (by positivity) (fun θ _ => hf θ)

end Yau.Blueprint.V03Proof
