import Yau.Proofs.E02EnvelopeBounds
import Yau.Proofs.E02ProductGap
import Yau.Proofs.E02ProductCost
import Yau.Proofs.E02Optimizer

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

def actualProductGap {n m : ℕ} (X : KahlerManifold n) (h : Flow X)
    (T : ℝ) (x : Pt X) (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q : ProductPoint n m) : ℝ :=
  (∑ i, α i*chartEnvelopeReal X h T x (Q.1,Q.2.2 i,Q.2.1))-
    productCostPhysical f α P₀ θ Q

/-- Actual ellipsoid feasibility supplies every scalar support bound
for the SAME original finite real envelope. -/
theorem actual_envelope_feasible_lower {n : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z η : ComplexVector n) (t : ℝ) (B : Herm n)
    (hDom : (z,η,t) ∈ envelopeDomain X T x)
    (hB : FeasibleEllipsoid X h T x z t B) :
    qform B η ≤ chartEnvelopeReal X h T x (z,η,t) := by
  have hBound := hB.2 η
  rw [←(chartEnvelopeReal_finite_bounds X h T x (z,η,t) hDom).2.2.1] at hBound
  exact EReal.coe_le_coe_iff.mp hBound

/-- The original product gap is nonnegative, and zero gives the full
Gram/projector equality orbit. No continuous optimizer is selected. -/
theorem actual_product_gap_support {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (M₀ : Rect n m) (hM₀ : (M₀*M₀ᴴ).PosDef) (θ : ℝ) (hθ : 0 < θ)
    (Q : ProductPoint n m) (hz : Q.1 ∈ chartTarget x) (ht : Q.2.1 ∈ Ioo 0 T)
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x Q.1 Q.2.1 B)
    (hMax : ∀ D, FeasibleEllipsoid X h T x Q.1 Q.2.1 D → D.det.re ≤ B.det.re)
    (hTouch : f (Q.1,Q.2.1) ≤ ellipsoidLogDet X h T x Q.1 Q.2.1) :
    0 ≤ actualProductGap X h T x f α (rowProjector M₀) θ Q ∧
      (actualProductGap X h T x f α (rowProjector M₀) θ Q = 0 →
        f (Q.1,Q.2.1) = ellipsoidLogDet X h T x Q.1 Q.2.1 ∧
        weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ = B⁻¹ ∧
        rowProjector (weightedColumns α Q.2.2) = rowProjector M₀) := by
  have hLog := ellipsoidLogDet_eq_log_det_of_max X h T x Q.1 Q.2.1 B hB hMax
  have hTrace : (Matrix.trace (B*(weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ))).re ≤
      ∑ i, α i*chartEnvelopeReal X h T x (Q.1,Q.2.2 i,Q.2.1) := by
    rw [weightedColumns_gram α Q.2.2 hα,trace_weighted_outer_products]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (actual_envelope_feasible_lower X h T x Q.1 (Q.2.2 i) Q.2.1 B ⟨hz,ht⟩ hB) (hα i))
  have hCompare := matrixSupportGap_nonneg_eq B hB.1 M₀ (weightedColumns α Q.2.2)
    hM₀ hM _ (f (Q.1,Q.2.1)) θ hθ (hTouch.trans_eq hLog) hTrace
  have hGap : actualProductGap X h T x f α (rowProjector M₀) θ Q =
      matrixSupportGap (∑ i, α i*chartEnvelopeReal X h T x (Q.1,Q.2.2 i,Q.2.1))
        (f (Q.1,Q.2.1)) θ M₀ (weightedColumns α Q.2.2) := rfl
  rw [hGap]
  refine ⟨hCompare.1,?_⟩
  intro hZero
  have hEq := hCompare.2 hZero
  exact ⟨hEq.1.trans hLog.symm,hEq.2.1,hEq.2.2.1⟩

end Yau.NodeProofs.E02Aux
