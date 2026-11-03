import Yau.Proofs.F05SmoothInverseChart
import Yau.LeafProofs.L16ChartOperatorAlgebra

/-! An explicit invertible coordinate replacement straightens the actual defining function. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.LeafProofs.L16Aux

def replaceCoordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L a : E →L[ℝ] ℝ) (v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (L-a).smulRight v

theorem replaceCoordinate_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L a : E →L[ℝ] ℝ) (v y : E) : replaceCoordinate L a v y = y + (L y-a y) • v := by
  rfl

theorem coordinate_replaceCoordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L a : E →L[ℝ] ℝ) (v y : E) (hav : a v = 1) :
    a (replaceCoordinate L a v y) = L y := by
  simp only [replaceCoordinate_apply, map_add, map_smul, hav, smul_eq_mul, mul_one]
  ring

theorem replaceCoordinate_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L a : E →L[ℝ] ℝ) (v : E) (hav : a v = 1) (hLv : L v ≠ 0) :
    Function.Injective (replaceCoordinate L a v) := by
  apply (injective_iff_map_eq_zero (replaceCoordinate L a v).toLinearMap.toAddMonoidHom).mpr
  intro y hy
  change replaceCoordinate L a v y = 0 at hy
  have hLy : L y = 0 := by
    rw [← coordinate_replaceCoordinate L a v y hav, hy, map_zero]
  have hform : y = a y • v := by
    rw [replaceCoordinate_apply, hLy, zero_sub, neg_smul] at hy
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hy)
  have hay : a y = 0 := by
    have hprod : a y * L v = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← hform, hLy]
    exact (mul_eq_zero.mp hprod).resolve_right hLv
  rw [hform, hay, zero_smul]

def replaceCoordinateEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (L a : E →L[ℝ] ℝ) (v : E)
    (hav : a v = 1) (hLv : L v ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (replaceCoordinate L a v)
    (LinearMap.ker_eq_bot.mpr (replaceCoordinate_injective L a v hav hLv))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp
      (replaceCoordinate_injective L a v hav hLv)))

def coordinateFlatten {n : ℕ} (x : Space n) (j : RIdx n) (ρ : Space n → ℝ)
    (y : Space n) : Space n :=
  (y-x) + (ρ y-realCoord (y-x) j) • realVec j

theorem coordinateFlatten_level {n : ℕ} (x : Space n) (j : RIdx n)
    (ρ : Space n → ℝ) (y : Space n) : realCoord (coordinateFlatten x j ρ y) j = ρ y := by
  have hav : realCoordLinear j (realVec j) = 1 := by
    simp [realCoordLinear, realVec_norm]
  have hlin : realCoordLinear j (coordinateFlatten x j ρ y) = ρ y := by
    change realCoordLinear j ((y-x)+(ρ y-realCoord (y-x) j) • realVec j) = ρ y
    simp only [map_add, map_smul, hav, realCoordLinear_apply, smul_eq_mul, mul_one]
    ring
  simpa only [realCoordLinear_apply] using hlin

theorem coordinateFlatten_hasFDerivAt {n : ℕ} (x : Space n) (j : RIdx n)
    {ρ : Space n → ℝ} (hρ : DifferentiableAt ℝ ρ x) :
    HasFDerivAt (coordinateFlatten x j ρ)
      (replaceCoordinate (fderiv ℝ ρ x) (realCoordLinear j) (realVec j)) x := by
  unfold coordinateFlatten
  have hs : HasFDerivAt (fun y : Space n => y-x) (ContinuousLinearMap.id ℝ (Space n)) x :=
    (hasFDerivAt_id x).sub_const x
  have hlin := (realCoordLinear j).hasFDerivAt.comp x hs
  have hd := hs.add ((hρ.hasFDerivAt.sub hlin).smul_const (realVec j))
  simpa only [realCoordLinear_apply, replaceCoordinate,
    Pi.add_def, Pi.smul_def', Pi.sub_apply, Function.comp_def, ContinuousLinearMap.comp_id] using hd

theorem defining_function_smooth_coordinate_chart {n : ℕ} {ρ : Space n → ℝ}
    {V : Set (Space n)} (hV : IsOpen V) (hρ : ContDiffOn ℝ ∞ ρ V)
    {x : Space n} (hx : x ∈ V) (hρx : ρ x = 0) (hD : fderiv ℝ ρ x ≠ 0) :
    ∃ (j : RIdx n) (c : OpenPartialHomeomorph (Space n) (Space n)),
      x ∈ c.source ∧ c.source ⊆ V ∧ c x = 0 ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target ∧
      ∀ y, realCoord (c y) j = ρ y := by
  have hj : ∃ j : RIdx n, fderiv ℝ ρ x (realVec j) ≠ 0 := by
    by_contra! hzero
    apply hD
    ext y
    rw [realCovector_coordinate_expansion]
    simp only [hzero, mul_zero, Finset.sum_const_zero, ContinuousLinearMap.zero_apply]
  obtain ⟨j,hj⟩ := hj
  have hav : realCoordLinear j (realVec j) = 1 := by
    simp [realCoordLinear, realVec_norm]
  let L := replaceCoordinateEquiv (fderiv ℝ ρ x) (realCoordLinear j) (realVec j) hav hj
  have hshift : ContDiffOn ℝ ∞ (fun y : Space n => y-x) V := contDiffOn_id.sub contDiffOn_const
  have hflat : ContDiffOn ℝ ∞ (coordinateFlatten x j ρ) V := by
    unfold coordinateFlatten
    simpa only [Pi.add_def, Pi.smul_def', realCoordLinear_apply,
      Function.comp_def] using
      hshift.add ((hρ.sub ((realCoordLinear j).contDiff.contDiffOn.comp hshift
        (fun _ _ => mem_univ _))).smul (contDiffOn_const (c := realVec j)))
  have hflatD : HasFDerivAt (coordinateFlatten x j ρ) (L : Space n →L[ℝ] Space n) x := by
    simpa only [L, replaceCoordinateEquiv, ContinuousLinearEquiv.coe_ofBijective] using
      coordinateFlatten_hasFDerivAt x j ((hρ.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp))
  obtain ⟨c,hxc,hcV,hcf,hc,hci⟩ := smooth_inverse_chart hV hflat hx hflatD
  refine ⟨j,c,hxc,hcV,?_,hc,hci,?_⟩
  · rw [hcf]
    simp only [coordinateFlatten, sub_self, hρx, ← realCoordLinear_apply, map_zero,
      zero_smul, zero_add]
  · intro y
    rw [hcf]
    exact coordinateFlatten_level x j ρ y

end Yau.Proofs.F05Aux
