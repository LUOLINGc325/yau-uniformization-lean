import Yau.Geometry.Basic

/-!
Single-circle formulas for complex directional derivatives. The source norm is
unchanged, and the circle radius never requires a nonzero direction.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Holomorphic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def lineWeight (R θ : ℝ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Complex.I) / circleMap 0 R θ

theorem circleMap_ne_zero {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    circleMap 0 R θ ≠ 0 := by
  intro hz
  have he := norm_circleMap_zero R θ
  rw [hz, norm_zero, abs_of_pos hR] at he
  exact hR.ne he

theorem lineWeight_continuous {R : ℝ} (hR : 0 < R) : Continuous (lineWeight R) := by
  exact continuous_const.div (continuous_circleMap 0 R) (circleMap_ne_zero hR)

theorem lineWeight_norm {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ‖lineWeight R θ‖ = ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ / R := by
  simp [lineWeight, norm_circleMap_zero, abs_of_pos hR]

/-- A single compact buffer contains the entire family of closed complex discs. -/
theorem lineTube_mem_closedBall {a x v : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ closedBall a (ρ / 4)) {ζ : ℂ}
    (hζ : ζ ∈ closedBall 0 ((ρ / 4) / (1 + ‖v‖))) :
    x + ζ • v ∈ closedBall a (ρ / 2) := by
  have hd : 0 < 1 + ‖v‖ := by positivity
  have hR : 0 ≤ (ρ / 4) / (1 + ‖v‖) := by positivity
  have hz : ‖ζ‖ ≤ (ρ / 4) / (1 + ‖v‖) := by simpa using hζ
  have hprod : ((ρ / 4) / (1 + ‖v‖)) * ‖v‖ ≤ ρ / 4 := by
    calc
      _ ≤ ((ρ / 4) / (1 + ‖v‖)) * (1 + ‖v‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hR
      _ = _ := div_mul_cancel₀ _ hd.ne'
  apply mem_closedBall.mpr
  calc
    dist (x + ζ • v) a ≤ dist (x + ζ • v) x + dist x a := dist_triangle _ _ _
    _ = ‖ζ‖ * ‖v‖ + dist x a := by simp [dist_eq_norm, norm_smul]
    _ ≤ ρ / 4 + ρ / 4 := add_le_add
      ((mul_le_mul_of_nonneg_right hz (norm_nonneg _)).trans hprod) hx
    _ = ρ / 2 := by ring

omit [NormedSpace ℂ E] in
theorem exists_closedBall_subset {s : Set E} (hs : IsOpen s) {a : E} (ha : a ∈ s) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall a ρ ⊆ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds ha)
  refine ⟨ε / 2, by positivity, ?_⟩
  intro x hx
  apply hball
  exact lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith)

theorem circleMap_mem_closedBall {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    circleMap 0 R θ ∈ closedBall 0 R := by
  simp [mem_closedBall, norm_circleMap_zero, abs_of_pos hR]

theorem lineTube_mem {s : Set E} {a x v : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall a ρ ⊆ s) (hx : x ∈ closedBall a (ρ / 4))
    {ζ : ℂ} (hζ : ζ ∈ closedBall 0 ((ρ / 4) / (1 + ‖v‖))) :
    x + ζ • v ∈ s := by
  apply hsub
  apply mem_closedBall.mpr
  exact (mem_closedBall.mp (lineTube_mem_closedBall hρ hx hζ)).trans (by linarith)

/-- Banach-valued Cauchy formula on the actual affine complex line. -/
theorem directional_eq_lineIntegral {s : Set E} {f : E → F}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s)
    {x v : E} {R : ℝ} (hR : 0 < R)
    (hdisc : ∀ z ∈ closedBall (0 : ℂ) R, x + z • v ∈ s) :
    (∫ θ in Icc 0 (2 * Real.pi),
      lineWeight R θ • f (x + circleMap 0 R θ • v)) = fderiv ℂ f x v := by
  have hx : x ∈ s := by simpa using hdisc 0 (mem_closedBall_self hR.le)
  have hslice : DifferentiableOn ℂ (fun ζ : ℂ => f (x + ζ • v)) (closedBall 0 R) := by
    intro ζ hζ
    exact ((hf.differentiableAt (hs.mem_nhds (hdisc ζ hζ))).comp ζ
      ((differentiableAt_id.smul_const v).const_add x)).differentiableWithinAt
  have hline : HasDerivAt (fun ζ : ℂ => x + ζ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hfd : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
    simpa using (hf.differentiableAt (hs.mem_nhds hx)).hasFDerivAt
  have hderiv : deriv (fun ζ : ℂ => f (x + ζ • v)) 0 = fderiv ℂ f x v :=
    (hfd.comp_hasDerivAt 0 hline).deriv
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral hR hslice
  rw [hderiv] at hc
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ ζ in C(0, R), (1 / (ζ - 0) ^ 2) • f (x + ζ • v)) := by
      rw [circleIntegral_def_Icc, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with θ
      rw [deriv_circleMap]
      simp only [sub_zero, smul_smul]
      congr 1
      unfold lineWeight
      field_simp [circleMap_ne_zero hR θ]
    _ = _ := by
      rw [hc, smul_smul, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]

end Yau.LeafProofs.L17Holomorphic
