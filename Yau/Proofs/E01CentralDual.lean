import Yau.Proofs.E01ProductDualLevi
import Yau.Proofs.E01ChernContraction
import Yau.Proofs.G01BisectionalNormalization

/-! The original centered dual norm Levi identity and its actual initial-metric positivity. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ}

theorem centered_dualNorm_levi_identity {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (ξ a u : ComplexVector n) :
    (wirt (fun p => wirtBar (fun q : CotangentCoord n => (dualNormChart g.form x q.1 q.2 : ℂ))
      p (a, u)) (chartPt x x, ξ) (a, u)).re =
      ellipsoidQuadratic (gMat g.form x)⁻¹ᵀ
        (u - matrixFiberMap ((complexMatrixWirt (hMat g.form x) (chartPt x x) a)ᵀ *
          (gMat g.form x)⁻¹ᵀ) ξ) +
      bisectionalForm g.form x
        (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap (gMat g.form x)⁻¹ᵀ ξ)))) a := by
  have hs : MetricSmooth g.form := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g
  have hHerm := hMat_isHermitian g.form x
  have hH := hMat_contDiffOn g x
  have hdet : ∀ z ∈ chartTarget x, (hMat g.form x z).det ≠ 0 :=
    fun z hz => ((hMat_posDef g.form x z hz).isUnit.map Matrix.detMonoidHom).ne_zero
  have hz : chartPt x x ∈ chartTarget x :=
    mem_extChartAt_target (I := ComplexModel n) x
  have hid := dualNormMat_product_mixed (isOpen_extChartAt_target (I := ComplexModel n) x)
    (hMat g.form x) hHerm hH hdet (chartPt x x) hz ξ a u
  change (wirt (fun p => wirtBar (fun q : CotangentCoord n => (dualNormChart g.form x q.1 q.2 : ℂ))
      p (a, u)) (chartPt x x, ξ) (a, u)).re = _ at hid
  rw [hid]
  congr 1
  let K : Herm n := (gMat g.form x)⁻¹ᵀ
  let A : Herm n := complexMatrixWirt (hMat g.form x) (chartPt x x) a
  let B : Herm n := complexMatrixWirt (fun w => complexMatrixWirtBar (hMat g.form x) w a) (chartPt x x) a
  let R : Herm n := Aᵀ * K * (Aᴴ)ᵀ - Bᵀ
  have hK : K.IsHermitian := (hHerm (chartPt x x)).inv.transpose
  have hc := centered_chern_residual_contraction g.form hs x (matrixFiberMap K ξ) a
  rw [complexMatrixWirtBar_of_hermitian (hMat g.form x) hHerm] at hc
  change ellipsoidQuadratic (K * R * K) ξ = _
  calc
    ellipsoidQuadratic (K * R * K) ξ = ellipsoidQuadratic R (matrixFiberMap K ξ) := by
      rw [ellipsoidQuadratic_matrixFiberMap, hK.eq]
    _ = _ := hc

theorem initial_bisectionalForm_nonneg (X : KahlerManifold n) (x : Pt X)
    (c a : ComplexVector n) : 0 ≤ bisectionalForm X.metric.form x c a := by
  by_cases hc : c = 0
  · simp [hc, bisectionalForm]
  by_cases ha : a = 0
  · simp [ha, bisectionalForm]
  have hp : GriffithsPositive X.metric.form :=
    (G01Aux.paperPositive_iff_griffithsPositive X.metric.form
      (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) X.kahler_metric).mp
      X.positive_bisectional_curvature
  exact (hp x c a hc ha).le

theorem initial_centered_dual_levi_nonneg (X : KahlerManifold n)
    (x : Pt X) (ξ : ComplexVector n) (v : CotangentCoord n) :
    0 ≤ (wirt (fun p => wirtBar (fun q => (dualNormChart X.metric.form x q.1 q.2 : ℂ)) p v)
      (chartPt x x, ξ) v).re := by
  rcases v with ⟨a, u⟩
  rw [centered_dualNorm_levi_identity X.metric x ξ a u]
  exact add_nonneg
    (ellipsoidQuadratic_nonneg (gMat_posDef X.metric.form x).inv.transpose.posSemidef _)
    (initial_bisectionalForm_nonneg X x _ a)

end Yau.NodeProofs.E01Aux
