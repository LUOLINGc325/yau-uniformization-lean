import Yau.Proofs.C04BisectionalScalarQuadratic

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Proofs.C04BisectionalScalarAux
open Yau Yau.Blueprint Yau.NodeProofs Yau.LeafProofs
variable {n : ℕ}

theorem metricQuadratic_four_bounds (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) {u v : Fin n → ℂ}
    (hu : metricQuadratic H u ≤ 1) (hv : metricQuadratic H v ≤ 1) :
    metricQuadratic H (u+v) ≤ 4 ∧ metricQuadratic H (u-v) ≤ 4 ∧
      metricQuadratic H (u+Complex.I • v) ≤ 4 ∧
        metricQuadratic H (u-Complex.I • v) ≤ 4 := by
  have ha := metricQuadratic_add_sub_le H hH u v
  have hb := metricQuadratic_add_sub_le H hH u (Complex.I • v)
  rw [metricQuadratic_I] at hb
  exact ⟨by linarith [ha.1], by linarith [ha.2], by linarith [hb.1], by linarith [hb.2]⟩

/-- Two complex polarizations bound every mixed coefficient from the actual
nonnegative diagonal bisectional values. -/
theorem curvatureValue_unit_bound
    (C : Fin n → Fin n → Fin n → Fin n → ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (R : ℝ) (hR : 0 ≤ R)
    (hs : ∀ i j k l, star (C i j k l) = C j i l k)
    (hpos : ∀ u v, 0 ≤ (curvatureValue C u u v v).re)
    (hb : ∀ u v, (curvatureValue C u u v v).re ≤
      R * metricQuadratic H u * metricQuadratic H v)
    (u v w z : Fin n → ℂ)
    (hu : metricQuadratic H u ≤ 1) (hv : metricQuadratic H v ≤ 1)
    (hw : metricQuadratic H w ≤ 1) (hz : metricQuadratic H z ≤ 1) :
    ‖curvatureValue C u v w z‖ ≤ 16*R := by
  have hd (a b : Fin n → ℂ) (ha : metricQuadratic H a ≤ 4)
      (hbb : metricQuadratic H b ≤ 4) : ‖curvatureValue C a a b b‖ ≤ 16*R := by
    rw [curvatureValue_diagonal_real C hs a b, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hpos a b)]
    calc
      _ ≤ R*metricQuadratic H a*metricQuadratic H b := hb a b
      _ ≤ R*4*4 := mul_le_mul (mul_le_mul_of_nonneg_left ha hR) hbb
        (metricQuadratic_nonneg H hH b) (by positivity)
      _ = _ := by ring
  obtain ⟨hw₁,hw₂,hw₃,hw₄⟩ := metricQuadratic_four_bounds H hH hw hz
  have hd₁ (a : Fin n → ℂ) (ha : metricQuadratic H a ≤ 4) :
      ‖curvatureValue C a a w z‖ ≤ 16*R :=
    norm_le_of_polarization (curvatureValue_polarize_last C a a w z)
      (hd a (w+z) ha hw₁) (hd a (w-z) ha hw₂)
      (hd a (w+Complex.I • z) ha hw₃) (hd a (w-Complex.I • z) ha hw₄)
  obtain ⟨hu₁,hu₂,hu₃,hu₄⟩ := metricQuadratic_four_bounds H hH hu hv
  exact norm_le_of_polarization (curvatureValue_polarize_first C u v w z)
    (hd₁ (u+v) hu₁) (hd₁ (u-v) hu₂)
    (hd₁ (u+Complex.I • v) hu₃) (hd₁ (u-Complex.I • v) hu₄)

variable {M : ComplexManifold n}

theorem chernCurvature_unit_bound (k : HermitianField M) (hs : MetricSmooth k)
    (hk : KahlerClosed k) (hBC : NonnegBisectional k) (x : M.Carrier)
    (u v w z : Fin n → ℂ)
    (hu : metricQuadratic (gMat k x) u ≤ 1) (hv : metricQuadratic (gMat k x) v ≤ 1)
    (hw : metricQuadratic (gMat k x) w ≤ 1) (hz : metricQuadratic (gMat k x) z ≤ 1) :
    ‖curvatureValue (chernCurvature k x) u v w z‖ ≤ 16*scalarCurvature k x := by
  exact curvatureValue_unit_bound (chernCurvature k x) (gMat k x)
    (L12Aux.hMat_posDef k x _ (mem_extChartAt_target x)).posSemidef
    (scalarCurvature k x) (ricci_scalar_bounds k hs hk hBC x).2.1
    (P06Aux.chernInChart_star k hs x _ (mem_extChartAt_target x))
    (fun a b => hBC x (WithLp.toLp 2 a) (WithLp.toLp 2 b))
    (bisectional_le_scalar k hs hk hBC x) u v w z hu hv hw hz

end Yau.Proofs.C04BisectionalScalarAux
