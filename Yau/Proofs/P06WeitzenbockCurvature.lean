import Yau.Proofs.P06Weitzenbock
import Yau.Proofs.G04FormInnerMatrix
import Yau.Proofs.G01RealRmChern
import Yau.Proofs.G01BisectionalNormalization
import Yau.Proofs.G04TraceDerivative

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs L23Aux G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

section Finite
variable {ι : Type*} [Fintype ι]

theorem sum_three_cycle (F : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ p, F a b p) = ∑ p, ∑ a, ∑ b, F a b p := by
  calc
    _ = ∑ a, ∑ p, ∑ b, F a b p := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem weighted_contraction_exchange (H : ι → ι → ℝ)
    (F : ι → ι → ι → ℝ) (K : ι → ℝ) :
    (∑ p, (∑ a, ∑ b, H a b * F a b p) * K p) =
      ∑ a, ∑ b, H a b * ∑ p, F a b p * K p := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [sum_three_cycle]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Finite

/-- Raised Ricci of the original real Levi-Civita calculator. -/
def raisedRicci (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (d p : RIdx n) : ℝ :=
  ∑ q, (realMetricFn h c z)⁻¹ p q * L12Aux.realRicciMatrix h c z d q

theorem riemannCoeff_eq_raised_curvature4 (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b d p : RIdx n) :
    riemannCoeff h c z a b d p =
      ∑ q, (realMetricFn h c z)⁻¹ p q * L12Aux.curvature4 h c z a b d q := by
  let G := realMetricFn h c z
  let V : RIdx n → ℝ := fun l => riemannCoeff h c z a b d l
  have hsym : Gᵀ = G := L18Aux.realMetricFn_isSymm h c z
  have hInv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h c z hz).det_pos.ne')
  change V p = (G⁻¹ *ᵥ (Gᵀ *ᵥ V)) p
  rw [hsym, Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]

theorem realRicci_eq_curvature4_contraction (h : HermitianField M) (hs : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (d q : RIdx n) :
    L12Aux.realRicciMatrix h c z d q =
      -∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b * L12Aux.curvature4 h c z a d b q := by
  rw [← realRicciCoeff_eq_realRicciMatrix h c z hz]
  change (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b * L12Aux.curvature4 h c z a d q b) = _
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [curvature4_swap_last h hs c z hz a d q b]
  ring

theorem raisedRicci_eq_riemann_contraction (h : HermitianField M) (hs : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (d p : RIdx n) :
    raisedRicci h c z d p =
      -∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b * riemannCoeff h c z a d b p := by
  simp only [raisedRicci, realRicci_eq_curvature4_contraction h hs c hz,
    riemannCoeff_eq_raised_curvature4 h c hz, Finset.mul_sum, mul_neg,
    Finset.sum_neg_distrib]
  congr 1
  conv_rhs => rw [sum_three_cycle]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem riemann_bianchi_difference (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (a d e p : RIdx n) :
    riemannCoeff h c z a e d p - riemannCoeff h c z a d e p =
      riemannCoeff h c z d e a p := by
  have hb := L12Aux.riemannCoeff_firstBianchi h c z a e d p
  rw [L12Aux.riemannCoeff_swap h c z e d a p,
    L12Aux.riemannCoeff_swap h c z d a e p] at hb
  linarith

/-- The four curvature terms reduce to two actual raised Ricci actions and
one Riemann contraction. This is still valid on every real two-form. -/
theorem curvatureTwo_eq_ricci_contraction (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (d e : RIdx n) :
    curvatureTwoComponents h A c z ![d,e] =
      (∑ p, raisedRicci h c z d p * chartFormMatrix A c z p e) +
      (∑ p, raisedRicci h c z e p * chartFormMatrix A c z d p) +
      ∑ a, ∑ b, ∑ p, (realMetricFn h c z)⁻¹ a b *
        riemannCoeff h c z d e a p * chartFormMatrix A c z b p := by
  simp only [raisedRicci_eq_riemann_contraction h hs c hz,
    neg_mul, Finset.sum_neg_distrib]
  rw [weighted_contraction_exchange, weighted_contraction_exchange]
  simp only [curvatureTwoComponents, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [chartFormMatrix_skew A c z p d, ← riemann_bianchi_difference h c z a d e p]
  ring

section MatrixFinite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_three (R H K : Matrix ι ι ℝ) :
    Matrix.trace (R * H * K) = ∑ p, ∑ a, ∑ b, R p a * H a b * K b p := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]

theorem cross_contraction_trace (R H K : Matrix ι ι ℝ) :
    (∑ a, ∑ b, ∑ p, H a b * R p a * K b p) = Matrix.trace (R * H * K) := by
  rw [trace_three, sum_three_cycle]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end MatrixFinite

theorem curvatureTwo_eq_ricci_matrix (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (d e : RIdx n) :
    curvatureTwoComponents h A c z ![d,e] =
      (L12Aux.realRicciMatrix h c z * (realMetricFn h c z)⁻¹ * chartFormMatrix A c z +
        chartFormMatrix A c z * (realMetricFn h c z)⁻¹ * L12Aux.realRicciMatrix h c z) d e +
      Matrix.trace (L12Aux.curvatureMatrix h c z d e * (realMetricFn h c z)⁻¹ *
        chartFormMatrix A c z) := by
  rw [curvatureTwo_eq_ricci_contraction h hs A c hz]
  have h₁ : (∑ p, raisedRicci h c z d p * chartFormMatrix A c z p e) =
      (L12Aux.realRicciMatrix h c z * (realMetricFn h c z)⁻¹ * chartFormMatrix A c z) d e := by
    simp only [raisedRicci, Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [(L12Aux.realMetricFn_isSymm h c z).inv.apply p q]
    ring
  have h₂ : (∑ p, raisedRicci h c z e p * chartFormMatrix A c z d p) =
      (chartFormMatrix A c z * (realMetricFn h c z)⁻¹ * L12Aux.realRicciMatrix h c z) d e := by
    simp only [raisedRicci, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro p _
    rw [realRicciMatrix_symm h hs c z hz e q]
    ring
  rw [h₁, h₂, cross_contraction_trace]
  rfl

theorem rawReal_mul_J (B : Matrix (Fin n) (Fin n) ℂ) :
    G01Aux.rawReal B * L12Aux.jMatrix n = G01Aux.rawReal (Complex.I • B) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rw [L12Aux.mul_jMatrix]
  fin_cases a <;> fin_cases b <;>
    simp [G01Aux.rawReal, L12Aux.jSign, L12Aux.jIndex, Matrix.smul_apply,
      Complex.mul_re, Complex.mul_im]

theorem trace_rawReal_mul_J (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (G01Aux.rawReal B * L12Aux.jMatrix n) = -2 * (Matrix.trace B).im := by
  rw [rawReal_mul_J, G01Aux.rawReal_trace, Matrix.trace_smul]
  simp [smul_eq_mul, Complex.mul_re]

/-- Exact reduction of the cross term to a complex trace. The factors 2 of G
and of iota cancel here, rather than being absorbed into the reaction. -/
theorem curvature_cross_trace_complex (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (A : RealForm M 2) (h11 : RealOneOne A)
    (x : M.Carrier) (d e : RIdx n) :
    Matrix.trace (L12Aux.curvatureMatrix h x (chartPt x x) d e *
      (realMetricFn h x (chartPt x x))⁻¹ * realFormMatrix A x) =
      2 * (Matrix.trace (G01Aux.complexCurvatureRealDirections h x (chartPt x x) d e *
        (gMat h x)⁻¹ * formHermitianMatrix A x)).im := by
  rw [G01Aux.curvatureMatrix_eq_rawReal h hs hk x (chartPt x x) (mem_extChartAt_target x) d e,
    G01Aux.realMetricFn_inverse_eq h x (chartPt x x) (mem_extChartAt_target x),
    realFormMatrix_eq_raw A h11 x]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) = -1 by norm_num, neg_one_smul,
    Matrix.trace_neg]
  rw [← Matrix.mul_assoc, ← G01Aux.rawReal_mul,
    ← G01Aux.rawReal_mul, trace_rawReal_mul_J]
  change -(-2 * _) = _
  simp only [gMat]
  ring

end Yau.NodeProofs.P06Weitzenbock
