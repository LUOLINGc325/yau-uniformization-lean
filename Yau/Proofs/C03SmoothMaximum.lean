import Yau.LeafProofs.L22LeviAggregate
import Yau.LeafProofs.L22RegularizedMaxRestrict

/-! Smooth maximum gluing preserves actual Levi semipositivity and agrees
exactly with a separated branch. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false

theorem regularizedMax_eq_separated_coordinate
    {ι : Type*} [Fintype ι] (δ z : ι → ℝ) (i : ι)
    (hδ : ∀ j, 0 < δ j)
    (hgap : ∀ j, j ≠ i → z j + δ j ≤ z i - δ i) :
    regularizedMaxCoords δ z = z i := by
  classical
  letI : Nonempty ι := ⟨i⟩
  have heq (x : ι → ℝ) :
      finiteMaximum (z + x) * regularizedMaxProductKernel δ x =
        (z i + x i) * regularizedMaxProductKernel δ x := by
    by_cases hx : regularizedMaxProductKernel δ x = 0
    · simp only [hx, mul_zero]
    have hxs (j : ι) : |x j| < δ j :=
      regularizedMaxKernel_support_of_pos (hδ j)
        ((Finset.prod_ne_zero_iff.mp hx) j (Finset.mem_univ j))
    have hmax : finiteMaximum (z + x) = z i + x i := by
      apply le_antisymm
      · apply finiteMaximum_le
        intro j
        by_cases hji : j = i
        · simp only [hji, Pi.add_apply, le_refl]
        · have hj := hgap j hji
          have hxj := (abs_lt.mp (hxs j)).2
          have hxi := (abs_lt.mp (hxs i)).1
          change z j + x j ≤ z i + x i
          linarith
      · exact le_finiteMaximum (z + x) i
    rw [hmax]
  unfold regularizedMaxCoords
  simp_rw [heq, add_mul]
  rw [integral_add ((regularizedMaxProductKernel_integrable δ).const_mul _)
    (regularizedMaxProductKernel_integrable_mul δ (continuous_apply i)),
    integral_const_mul, regularizedMaxProductKernel_mass,
    regularizedMaxProductKernel_firstMoment, mul_one, add_zero]

theorem regularizedMax_complexLevi_nonneg
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → ℝ) {g : ι → ComplexVector n → ℝ} {z : ComplexVector n}
    (hg : ∀ i, ContDiffAt ℝ 2 (g i) z)
    (hpos : ∀ i v, 0 ≤ complexLeviQuadratic (g i) z v) (v : ComplexVector n) :
    0 ≤ complexLeviQuadratic (fun x => regularizedMaxCoords δ (fun i => g i x)) z v := by
  have hs : ContDiff ℝ 2 (regularizedMaxCoords δ) :=
    (regularizedMaxCoords_smooth δ).of_le (by simp)
  rw [complexLeviQuadratic_aggregate hg hs.contDiffAt]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg
      (fderiv_coordinate_nonneg (hs.differentiable (by norm_num) _)
        (regularizedMaxCoords_monotone δ) i) (hpos i v)
  · apply div_nonneg _ (by norm_num)
    exact add_nonneg
      (hessian_nonneg_of_convex hs (regularizedMaxCoords_convex δ) _ _)
      (hessian_nonneg_of_convex hs (regularizedMaxCoords_convex δ) _ _)

theorem regularizedMax_leviC_posSemidef
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → ℝ) {g : ι → ComplexVector n → ℝ} {z : ComplexVector n}
    (hg : ∀ i, ContDiffAt ℝ 2 (g i) z) (hpos : ∀ i, (leviC (g i) z).PosSemidef) :
    (leviC (fun x => regularizedMaxCoords δ (fun i => g i x)) z).PosSemidef := by
  apply (leviC_posSemidef_iff
    (((regularizedMaxCoords_smooth δ).of_le (by simp)).contDiffAt.comp z
      (contDiffAt_pi.mpr hg))).mpr
  exact regularizedMax_complexLevi_nonneg δ hg
    (fun i => (leviC_posSemidef_iff (hg i)).mp (hpos i))

end Yau.Proofs.C03Aux
