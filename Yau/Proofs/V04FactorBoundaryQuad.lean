import Yau.Proofs.V04MatrixUnitTests
import Yau.Proofs.V04MajorantOrder

/-! The boundary quadratic cost of the same inverse-factor unit column
is at most one for the actual original boundary symbol. -/

open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem quadValue_add (A B : CotangentMatrix n) (v : CotangentIndex n → ℂ) :
    quadValue (A + B) v = quadValue A v + quadValue B v := by
  simp only [quadValue, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem spectralFactor_unit_column_boundary_quad {d : VariationData X q}
    {j a : ℕ} {δ : ℝ} (hδ : 0 < δ) {F : VariationDisc X}
    {E H Hinv : ℂ → CotangentMatrix n} (hH : SpectralFactorFor d j a δ F E H Hinv)
    (hT : ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian)
    (v : EuclideanSpace ℂ (CotangentIndex n)) (hv : ‖v‖ ≤ 1) (θ : ℝ) :
    quadValue (boundarySymbol d j a F E (circlePoint θ))
      (Hinv (circlePoint θ) *ᵥ WithLp.ofLp v) ≤ 1 := by
  let A := boundarySymbol d j a F E (circlePoint θ)
  let l := Hinv (circlePoint θ) *ᵥ WithLp.ofLp v
  have hpos := smoothMajorant_ge_matrix_add_delta hδ A (hT θ)
  have hquad : 0 ≤ quadValue (smoothMajorant δ A -
      (A + (δ : ℂ) • (1 : CotangentMatrix n))) l := hpos.re_dotProduct_nonneg l
  rw [quadValue_sub, quadValue_add, quadValue_real_smul] at hquad
  have hI : 0 ≤ quadValue (1 : CotangentMatrix n) l :=
    Matrix.PosSemidef.one.re_dotProduct_nonneg l
  have hupper : quadValue A l ≤ quadValue (smoothMajorant δ A) l := by nlinarith
  have hcircle : circlePoint θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, circlePoint, Complex.norm_exp]
  have hnorm : quadValue (smoothMajorant δ A) l = ‖v‖ ^ 2 := by
    rw [← hH.2.2 θ]
    calc
      _ = quadValue (1 : CotangentMatrix n) (H (circlePoint θ) *ᵥ l) := by
        simpa only [Matrix.mul_one] using quadValue_congruence (1 : CotangentMatrix n)
          (H (circlePoint θ)) l
      _ = ‖v‖ ^ 2 := by
        dsimp [l]
        rw [Matrix.mulVec_mulVec, (hH.2.1 _ hcircle).1, Matrix.one_mulVec, quadValue_one]
  exact hupper.trans (hnorm.le.trans (by nlinarith [norm_nonneg v]))

end Yau.Blueprint.V04Proof
