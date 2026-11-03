import Yau.Proofs.V03EuclideanAreaVariation
import Yau.Proofs.V03AmbientVelocitySeminorm

/-! The actual Euclidean summand satisfies the original uniform mixed
derivative bound, with one constant before every realization. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem holomorphicColumn_boundaryDSq_ne_top
    {l : ℂ → CotangentIndex n → ℂ} (hl : HolomorphicColumn l) :
    boundaryDSq (fun θ => l (circlePoint θ)) ≠ ⊤ := by
  classical
  rw [boundaryDSq_eq_sum_singleton (fun θ => l (circlePoint θ))]
  apply ENNReal.sum_ne_top.mpr
  intro i _
  rw [boundaryDSq_scalar_eq_inverse_area (hl i)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (normDiscArea_ne_top_of_closedDisc (hl i))

theorem realized_euclideanArea_mixed {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    mixedReal (fun z => (euclideanArea (fun ζ => d.G (fz z ζ))).toReal) =
      (2 * Real.pi) * (boundaryDSq (fun θ b =>
        ambientVelocity d F E l h α (circlePoint θ) b)).toReal := by
  let U : Set ℂ := Metric.ball 0 R
  let H : ℂ × ℂ → ComplexVector q := fun p => d.G (fz p.1 p.2)
  have h0 : (0 : ℂ) ∈ U := Metric.mem_ball_self hR.1.1
  have hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    cotangentHolomorphicOn_ambient_contDiffOn hR.1.2.2 hd.2.2.2.2.1.1
  have heq : (fun θ b => fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)
      (0, circlePoint θ) (1, 0) b) =
      (fun θ b => ambientVelocity d F E l h α (circlePoint θ) b) := by
    funext θ b
    have hh := fderiv_complex_parameter_slice (U := U) Metric.isOpen_ball h0
      (circlePoint_mem_closedBall θ)
      ((hH.differentiableOn (by simp)) _ ⟨h0, circlePoint_mem_closedBall θ⟩) (1 : ℂ)
    rw [← hh]
    exact congrArg (fun v : ComplexVector q => v b)
      (realizes_ambient_first_derivative d hd j a F E l h α fz R hR _
        (circlePoint_mem_closedBall θ))
  rw [← heq]
  exact euclideanFamilyArea_mixed (H := H) Metric.isOpen_ball h0 hH

theorem actualEuclideanEnergyDerivative {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      |mixedReal (fun z => (euclideanArea (fun ζ => d.G (fz z ζ))).toReal)| ≤
        C * (1 + (variationEnergy d j F).toReal +
          (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨C, hC, hbound⟩ := ambientVelocity_uniform_boundaryDSq hd j a L hL
  refine ⟨(2 * Real.pi) * C, mul_nonneg (by positivity) hC,
    fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  have hDl := holomorphicColumn_boundaryDSq_ne_top hl
  have hEn : variationEnergy d j F ≠ ⊤ := hF.2.2.2.2.2.2.2.2
  have hsum : 1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ)) ≠ ⊤ := by
    finiteness
  have hright : ENNReal.ofReal C *
      (1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
  have hv := ENNReal.toReal_mono hright (hbound F E l h α fz R hF hE hl hlL hR)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_add (by finiteness : 1 + variationEnergy d j F ≠ ⊤) hDl,
    ENNReal.toReal_add ENNReal.one_ne_top hEn, ENNReal.toReal_one] at hv
  rw [realized_euclideanArea_mixed hd j a F E l h α fz R hR,
    abs_of_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg)]
  calc
    _ ≤ (2 * Real.pi) * (C * (1 + (variationEnergy d j F).toReal +
        (boundaryDSq (fun θ => l (circlePoint θ))).toReal)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by ring

theorem realized_clockArea_mixed (F : VariationDisc X)
    (fz : ℂ → ℂ → CotangentPoint X.manifold) :
    mixedReal (fun z => (clockArea {F with f := fz z}).toReal) = 0 := by
  simp [clockArea, mixedReal, wirt, wirtBar]

end Yau.Blueprint.V03Proof
