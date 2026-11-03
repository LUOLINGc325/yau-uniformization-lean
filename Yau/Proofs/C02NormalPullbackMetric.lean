import Yau.Proofs.C02NormalDifferentialSmooth
import Yau.Proofs.C02FrameBounds

/-! The real pullback metric of the actual normal map, reconstructed through
the genuine parallel isometry. No chosen chart or replacement metric occurs. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalGaugeMetric (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  let B := normalDifferential g p U hU x
  ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).flip B).comp
    ((innerSL ℝ).comp B)

theorem normalGaugeMetric_apply (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x u v : ComplexVector n) :
    normalGaugeMetric g p U hU x u v =
      ⟪normalDifferential g p U hU x u, normalDifferential g p U hU x v⟫_ℝ := rfl

theorem normalGaugeMetric_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    ContDiff ℝ ∞ (normalGaugeMetric g p U hU) := by
  rw [← contDiffOn_univ]
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  have hB := normalDifferential_smooth g p U hU
  simpa only [normalGaugeMetric_apply] using
    ((hB.clm_apply (contDiff_const (c := u))).inner ℝ
      (hB.clm_apply (contDiff_const (c := v)))).contDiffOn

theorem normalGaugeMetric_eq_pullback (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x u v : ComplexVector n) :
    normalGaugeMetric g p U hU x u v =
      (underlyingRealRiemannianMetric g.form).inner (normalRealMap g p U x)
        (rawNormalDifferential g p U x u) (rawNormalDifferential g p U x v) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  change ⟪normalDifferential g p U hU x u, normalDifferential g p U hU x v⟫_ℝ =
    ⟪rawNormalDifferential g p U x u, rawNormalDifferential g p U x v⟫_ℝ
  rw [← normalDifferential_reconstruct g p U hU x u,
    ← normalDifferential_reconstruct g p U hU x v,
    (normalParallelIsometry g p U hU x).inner_map_map]

theorem normalGaugeMetric_bounds_of_close_identity (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x : ComplexVector n)
    (hB : ‖normalDifferential g p U hU x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4)
    (u : ComplexVector n) :
    (1 / 4 : ℝ) * ‖u‖ ^ 2 ≤ normalGaugeMetric g p U hU x u u ∧
      normalGaugeMetric g p U hU x u u ≤ (9 / 4 : ℝ) * ‖u‖ ^ 2 := by
  simpa only [normalGaugeMetric_apply, real_inner_self_eq_norm_sq] using
    close_identity_squared_bounds (normalDifferential g p U hU x) hB u

end Yau.Blueprint.C02Proof
