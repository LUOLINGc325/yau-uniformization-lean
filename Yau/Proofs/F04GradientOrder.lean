import Yau.Proofs.F04InverseOrder
import Yau.LeafProofs.L14

open scoped Matrix ComplexOrder Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem hermitianField_real_quadratic_order (A B : HermitianField M)
    (x : M.Carrier) (hAB : HermLE (gMat A x) (gMat B x)) (w : TangentVector M x) :
    ((A x).toFun w w).re ≤ ((B x).toFun w w).re := by
  let b := Yau.LeafProofs.chartFrameBasis x x (mem_extChartAt_source x)
  have hcoords (H : HermitianField M) :
      star (b.repr w) ⬝ᵥ (gMat H x *ᵥ b.repr w) = (H x).toFun w w := by
    rw [Yau.LeafProofs.gMat_eq_frameGram, Yau.LeafProofs.frameGram_eq_hermitianGram H x x
      (mem_extChartAt_source x)]
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc] using
      Yau.LeafProofs.hermitian_coordinates (H x) b w w
  have hn := (show (gMat B x - gMat A x).PosSemidef from hAB).dotProduct_mulVec_nonneg (b.repr w)
  rw [Matrix.sub_mulVec, dotProduct_sub, hcoords, hcoords] at hn
  have hre := (Complex.nonneg_iff.mp hn).1
  simpa only [Complex.sub_re, sub_nonneg] using hre

theorem realMetricFn_order (A B : HermitianField M)
    (hAB : ∀ x, HermLE (gMat A x) (gMat B x))
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    (realMetricFn B c z - realMetricFn A c z).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨(Yau.LeafProofs.L12Aux.realMetricFn_posDef B c z hz).isHermitian.sub
    (Yau.LeafProofs.L12Aux.realMetricFn_posDef A c z hz).isHermitian, ?_⟩
  intro r
  rw [Matrix.sub_mulVec, dotProduct_sub,
    Yau.LeafProofs.L12Aux.realMetricFn_quadratic,
    Yau.LeafProofs.L12Aux.realMetricFn_quadratic,
    Yau.LeafProofs.L12Aux.hermitianRealBilin_apply,
    Yau.LeafProofs.L12Aux.hermitianRealBilin_apply]
  have ho := hermitianField_real_quadratic_order A B (chartInv c z) (hAB _)
    (chartVec c (chartInv c z) (∑ a, r a • realVec a))
  linarith

theorem chartGradientPair_dotProduct (H : HermitianField M) (c : M.Carrier)
    (f k : ComplexVector n → ℝ) (z : ComplexVector n) :
    Yau.LeafProofs.L18Aux.chartGradientPair H c f k z =
      dotProduct (fun i => rDeriv f z i)
        ((realMetricFn H c z)⁻¹ *ᵥ (fun j => rDeriv k z j)) := by
  rw [Yau.LeafProofs.L18Aux.chartGradientPair_eq_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cotangent energy increases when the actual Hermitian metric decreases. -/
theorem scalarGradientPair_inverse_order (A B : HermitianField M)
    (hAB : ∀ x, HermLE (gMat A x) (gMat B x)) (f : M.Carrier → ℝ) (x : M.Carrier) :
    Yau.LeafProofs.L18Aux.scalarGradientPair B f f x ≤
      Yau.LeafProofs.L18Aux.scalarGradientPair A f f x := by
  unfold Yau.LeafProofs.L18Aux.scalarGradientPair
  rw [chartGradientPair_dotProduct, chartGradientPair_dotProduct]
  exact real_inverse_quadratic_order
    (Yau.LeafProofs.L12Aux.realMetricFn_posDef A x (chartPt x x) (mem_extChartAt_target x))
    (Yau.LeafProofs.L12Aux.realMetricFn_posDef B x (chartPt x x) (mem_extChartAt_target x))
    (realMetricFn_order A B hAB x (mem_extChartAt_target x)) _

theorem flow_scalarGradientPair_lower_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {t : ℝ} (ht : 0 ≤ t)
    (f : Pt X → ℝ) (x : Pt X) :
    Yau.LeafProofs.L18Aux.scalarGradientPair X.metric.form f f x ≤
      Yau.LeafProofs.L18Aux.scalarGradientPair (h t) f f x :=
  scalarGradientPair_inverse_order (h t) X.metric.form (hloc.2.2.2.2.1 t ht) f x

end Yau.F04Proof
