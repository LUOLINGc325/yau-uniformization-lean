import Yau.LeafProofs.L16ExpBoundaryLogEquation

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

def definingBarrier {n : ℕ} (s : Space n → ℝ) (κ : ℝ) (x : Space n) : ℝ :=
  1-Real.exp (-κ*s x)

theorem d_exp {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (i : Yau.RIdx n) :
    d (fun y => Real.exp (f y)) x i = Real.exp (f x)*d f x i := by
  simp only [d, fderiv_exp hf, smul_apply, smul_eq_mul]

theorem definingBarrier_contDiffAt {n : ℕ} {s : Space n → ℝ} {κ : ℝ}
    {x : Space n} (hs : ContDiffAt ℝ 2 s x) :
    ContDiffAt ℝ 2 (definingBarrier s κ) x := by
  change ContDiffAt ℝ 2 (fun y => 1-Real.exp (-κ*s y)) x
  exact contDiffAt_const.sub ((contDiffAt_const.mul hs).exp)

theorem d_definingBarrier {n : ℕ} {s : Space n → ℝ} {κ : ℝ}
    {x : Space n} (hs : DifferentiableAt ℝ s x) (i : Yau.RIdx n) :
    d (definingBarrier s κ) x i = κ*Real.exp (-κ*s x)*d s x i := by
  have he : DifferentiableAt ℝ (fun y => -κ*s y) x := hs.const_mul (-κ)
  change fderiv ℝ (fun y => 1-Real.exp (-κ*s y)) x (Yau.realVec i) =
    κ*Real.exp (-κ*s x)*fderiv ℝ s x (Yau.realVec i)
  simp only [fderiv_const_sub,fderiv_exp he,
    fderiv_const_mul hs,smul_apply,smul_eq_mul,neg_apply]
  ring

/-- The actual coordinate Hessian of the defining-function exponential. -/
theorem secondFDeriv_definingBarrier {n : ℕ} {s : Space n → ℝ} {κ : ℝ}
    {x : Space n} (hs : ContDiffAt ℝ 2 s x) (i j : Yau.RIdx n) :
    fderiv ℝ (fderiv ℝ (definingBarrier s κ)) x (Yau.realVec i) (Yau.realVec j) =
      κ*Real.exp (-κ*s x)*fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j) -
        κ^2*Real.exp (-κ*s x)*d s x i*d s x j := by
  have hJ := definingBarrier_contDiffAt (κ := κ) hs
  have heq : (fun y => d (definingBarrier s κ) y j) =ᶠ[𝓝 x]
      fun y => κ*Real.exp (-κ*s y)*d s y j := by
    filter_upwards [hs.eventually (by norm_num)] with y hy
    exact d_definingBarrier (hy.differentiableAt (by norm_num)) j
  have hd := congrArg (fun L : Space n →L[ℝ] ℝ => L (Yau.realVec i)) heq.fderiv_eq
  change d (fun y => d (definingBarrier s κ) y j) x i =
    d (fun y => κ*Real.exp (-κ*s y)*d s y j) x i at hd
  rw [d_d hJ] at hd
  rw [hd]
  have hsD := hs.differentiableAt (by norm_num)
  have heD : DifferentiableAt ℝ (fun y => Real.exp (-κ*s y)) x :=
    (hsD.const_mul (-κ)).exp
  rw [d_mul (f := fun y => κ*Real.exp (-κ*s y))
    (heD.const_mul κ) (differentiableAt_d hs j),d_d hs]
  have hc : d (fun y => κ*Real.exp (-κ*s y)) x i =
      -κ^2*Real.exp (-κ*s x)*d s x i := by
    simp only [d,fderiv_const_mul heD,fderiv_exp (hsD.const_mul (-κ)),
      fderiv_const_mul hsD,smul_apply,smul_eq_mul]
    ring
  rw [hc]
  ring

theorem definingBarrier_nonneg {n : ℕ} {s : Space n → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) {x : Space n} (hs : 0 ≤ s x) : 0 ≤ definingBarrier s κ x := by
  have he : Real.exp (-κ*s x) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  exact sub_nonneg.mpr he

theorem definingBarrier_le_linear {n : ℕ} {s : Space n → ℝ} {κ : ℝ}
    (x : Space n) : definingBarrier s κ x ≤ κ*s x := by
  have h := Real.add_one_le_exp (-κ*s x)
  dsimp only [definingBarrier]
  linarith

/-- The elliptic contraction of the exponential contains the positive
quadratic gradient term with its exact coefficient and sign. -/
theorem definingBarrier_operator_identity {n : ℕ} {s : Space n → ℝ} {κ : ℝ}
    {x : Space n} (hs : ContDiffAt ℝ 2 s x)
    (A : Mat n) (β : Yau.RIdx n → ℝ) :
    -(∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ (definingBarrier s κ)) x
        (Yau.realVec i) (Yau.realVec j)) - (∑ i, β i*d (definingBarrier s κ) x i) =
      κ*Real.exp (-κ*s x)*
        (κ*(∑ i, ∑ j, A i j*d s x i*d s x j) -
          (∑ i, ∑ j, A i j*fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j)) -
          ∑ i, β i*d s x i) := by
  simp only [secondFDeriv_definingBarrier hs,
    d_definingBarrier (hs.differentiableAt (by norm_num))]
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  ring_nf
  have hcomm :
      (∑ i, ∑ j, A i j*κ*Real.exp (-(κ*s x))*
        fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j)) =
      ∑ i, ∑ j, κ*Real.exp (-(κ*s x))*A i j*
        fderiv ℝ (fderiv ℝ s) x (Yau.realVec i) (Yau.realVec j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcomm]
  ring

end Yau.LeafProofs.L16ExpBoundaryAux
