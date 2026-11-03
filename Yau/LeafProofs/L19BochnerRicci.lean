import Yau.LeafProofs.L19BochnerCommutator

/-! The curvature contraction in the Bochner formula is the project's
actual Levi--Civita Ricci matrix, with its positive sign fixed explicitly. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux L12Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem curvature4_raise_last (g : SmoothMetric M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (l i k p : RIdx n) :
    riemannCoeff g.form a z l i k p =
      ∑ b, (realMetricFn g.form a z)⁻¹ p b * curvature4 g.form a z l i k b := by
  let G := realMetricFn g.form a z
  let v : RIdx n → ℝ := fun q => riemannCoeff g.form a z l i k q
  have hGsym : Gᵀ = G := L18Aux.realMetricFn_isSymm g.form a z
  have hunit : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef g.form a z hz).det_pos.ne'
  have hAG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit
  change v p = (G⁻¹ *ᵥ (Gᵀ *ᵥ v)) p
  rw [hGsym, Matrix.mulVec_mulVec, hAG, Matrix.one_mulVec]

theorem inverseMetric_curvature4_contract (g : SmoothMetric M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (i b : RIdx n) :
    (∑ l, ∑ k, (realMetricFn g.form a z)⁻¹ l k * curvature4 g.form a z l i b k) =
      realRicciMatrix g.form a z i b := by
  let G := realMetricFn g.form a z
  have hGsym : Gᵀ = G := L18Aux.realMetricFn_isSymm g.form a z
  have hunit : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef g.form a z hz).det_pos.ne'
  have hAG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit
  have hrow (l : RIdx n) : (∑ k, G⁻¹ l k * curvature4 g.form a z l i b k) =
      riemannCoeff g.form a z l i b l := by
    let R := curvatureMatrix g.form a z l i
    change (G⁻¹ * (Gᵀ * R)) l b = R l b
    rw [hGsym, ← Matrix.mul_assoc, hAG, Matrix.one_mul]
  change (∑ l, ∑ k, G⁻¹ l k * curvature4 g.form a z l i b k) = _
  simp_rw [hrow]
  rfl

/-- Raising, using the actual last-slot curvature skew symmetry, and
contracting with the genuine inverse metric gives the positive Ricci term. -/
theorem inverseMetric_curvature_contract_ricci (g : SmoothMetric M) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) (i p : RIdx n) :
    -(∑ l, ∑ k, (realMetricFn g.form a z)⁻¹ l k * riemannCoeff g.form a z l i k p) =
      ∑ b, (realMetricFn g.form a z)⁻¹ p b * realRicciMatrix g.form a z i b := by
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn g.form a z)⁻¹
  have hraise : (∑ l, ∑ k, A l k * riemannCoeff g.form a z l i k p) =
      ∑ l, ∑ k, ∑ b, A p b * (A l k * curvature4 g.form a z l i k b) := by
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    rw [curvature4_raise_last g a hz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hskew (b : RIdx n) :
      (∑ l, ∑ k, A l k * curvature4 g.form a z l i k b) =
        -(∑ l, ∑ k, A l k * curvature4 g.form a z l i b k) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    rw [curvature4_swap_last g a z hz l i k b]
    ring
  change -(∑ l, ∑ k, A l k * riemannCoeff g.form a z l i k p) = _
  rw [hraise, sum_three_cycle]
  simp only [← Finset.mul_sum]
  simp_rw [hskew]
  simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun V : ℝ => A p b * V) (inverseMetric_curvature4_contract g a hz i b)

end Yau.LeafProofs.L19Aux
