import Yau.LeafProofs.L16ExpBoundarySphere
import Yau.LeafProofs.L16ExpBoundaryComparison

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem secondFDeriv_add_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y+g y)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w+fderiv ℝ (fderiv ℝ g) x v w := by
  have h := congrArg (fun A => A ![v,w]) (iteratedFDeriv_add_apply hf hg)
  simpa only [Pi.add_def,iteratedFDeriv_two_apply,add_apply,Pi.add_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem secondFDeriv_const_mul_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => c*f y)) x v w =
      c*fderiv ℝ (fderiv ℝ f) x v w := by
  have h := congrArg (fun A => A ![v,w]) (iteratedFDeriv_const_smul_apply (a := c) hf)
  simpa only [Pi.smul_def,iteratedFDeriv_two_apply,smul_apply,Pi.smul_apply,
    smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem stationaryOp_add {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (A : Mat n) (β : Yau.RIdx n → ℝ) :
    stationaryOp A β (fun y => f y+g y) x = stationaryOp A β f x+stationaryOp A β g x := by
  simp only [stationaryOp,secondFDeriv_add_at hf hg,d,
    fderiv_fun_add (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num)),
    add_apply,mul_add,Finset.sum_add_distrib]
  ring

theorem stationaryOp_const_mul {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (A : Mat n) (β : Yau.RIdx n → ℝ) (c : ℝ) :
    stationaryOp A β (fun y => c*f y) x = c*stationaryOp A β f x := by
  simp only [stationaryOp,secondFDeriv_const_mul_at hf,d,
    fderiv_const_mul (hf.differentiableAt (by norm_num)),smul_apply,smul_eq_mul]
  have hH : (∑ i, ∑ j, A i j*(c*fderiv ℝ (fderiv ℝ f) x (Yau.realVec i) (Yau.realVec j))) =
      c*(∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ f) x (Yau.realVec i) (Yau.realVec j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hD : (∑ i, β i*(c*fderiv ℝ f x (Yau.realVec i))) =
      c*(∑ i, β i*fderiv ℝ f x (Yau.realVec i)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hH,hD]
  ring

def combinedBarrier {n : ℕ} (s : Space n → ℝ) (κ K c : ℝ) (y x : Space n) : ℝ :=
  K*definingBarrier s κ x+c*sphereBarrier y x

theorem combinedBarrier_contDiffAt {n : ℕ} {s : Space n → ℝ} {κ K c : ℝ}
    {y x : Space n} (hs : ContDiffAt ℝ 2 s x) :
    ContDiffAt ℝ 2 (combinedBarrier s κ K c y) x := by
  change ContDiffAt ℝ 2 (fun z => K*definingBarrier s κ z+c*sphereBarrier y z) x
  exact (contDiffAt_const.mul (definingBarrier_contDiffAt hs)).add
    (contDiffAt_const.mul ((sphereBarrier_contDiff y).contDiffAt.of_le (by simp)))

theorem combinedBarrier_operator {n : ℕ} {s : Space n → ℝ} {κ K c : ℝ}
    {y x : Space n} (hs : ContDiffAt ℝ 2 s x) (A : Mat n) (β : Yau.RIdx n → ℝ) :
    stationaryOp A β (combinedBarrier s κ K c y) x =
      K*stationaryOp A β (definingBarrier s κ) x+c*stationaryOp A β (sphereBarrier y) x := by
  change stationaryOp A β (fun z => K*definingBarrier s κ z+c*sphereBarrier y z) x = _
  rw [stationaryOp_add (contDiffAt_const.mul (definingBarrier_contDiffAt hs))
    (contDiffAt_const.mul ((sphereBarrier_contDiff y).contDiffAt.of_le (by simp))),
    stationaryOp_const_mul (definingBarrier_contDiffAt hs),
    stationaryOp_const_mul ((sphereBarrier_contDiff y).contDiffAt.of_le (by simp))]

theorem combinedBarrier_nonneg {n : ℕ} {s : Space n → ℝ} {κ K c : ℝ}
    {y x : Space n} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hc : 0 ≤ c) (hs : 0 ≤ s x) :
    0 ≤ combinedBarrier s κ K c y x :=
  add_nonneg (mul_nonneg hK (definingBarrier_nonneg hκ hs)) (mul_nonneg hc (sq_nonneg _))

theorem combinedBarrier_on_sphere {n : ℕ} {s : Space n → ℝ} {κ K W₀ r : ℝ}
    {y x : Space n} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hr : 0 < r)
    (hs : 0 ≤ s x) (hxy : ‖x-y‖ = r) :
    W₀ ≤ combinedBarrier s κ K (W₀/r^2) y x := by
  have hJ := mul_nonneg hK (definingBarrier_nonneg hκ hs)
  have hc : W₀/r^2*sphereBarrier y x = W₀ := by
    dsimp [sphereBarrier]
    rw [hxy]
    field_simp
  dsimp only [combinedBarrier]
  rw [hc]
  linarith

theorem combinedBarrier_le_linear {n : ℕ} {s : Space n → ℝ} {κ K W₀ r M₁ : ℝ}
    {y x : Space n} (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hW₀ : 0 ≤ W₀) (hr : 0 < r)
    (hs : s x ≤ M₁*‖x-y‖) (hxy : ‖x-y‖ ≤ r) :
    combinedBarrier s κ K (W₀/r^2) y x ≤ (K*κ*M₁+W₀/r)*‖x-y‖ := by
  have hJ : K*definingBarrier s κ x ≤ K*κ*M₁*‖x-y‖ := by
    have h := mul_le_mul_of_nonneg_left (definingBarrier_le_linear (s := s) (κ := κ) x) hK
    have h' := mul_le_mul_of_nonneg_left hs (mul_nonneg hK hκ)
    nlinarith
  have hc : 0 ≤ W₀/r^2 := by positivity
  have hcr : (W₀/r^2)*r = W₀/r := by field_simp
  have hSq := mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (x-y)] : ‖x-y‖^2 ≤ r*‖x-y‖) hc
  rw [← mul_assoc,hcr] at hSq
  dsimp only [combinedBarrier,sphereBarrier]
  nlinarith

theorem combinedBarrier_operator_lower_bound {n : ℕ} {s : Space n → ℝ}
    {κ K c μ C H : ℝ} {y x : Space n} (hs : ContDiffAt ℝ 2 s x)
    {A : Mat n} {β : Yau.RIdx n → ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hJ : μ ≤ stationaryOp A β (definingBarrier s κ) x)
    (hSphere : |stationaryOp A β (sphereBarrier y) x| ≤ C)
    (hConst : H+c*C ≤ K*μ) :
    H ≤ stationaryOp A β (combinedBarrier s κ K c y) x := by
  rw [combinedBarrier_operator hs]
  have h₁ := mul_le_mul_of_nonneg_left hJ hK
  have h₂ := mul_le_mul_of_nonneg_left (abs_le.mp hSphere).1 hc
  nlinarith

end Yau.LeafProofs.L16ExpBoundaryAux
