import Yau.LeafProofs.L16ExpBoundaryLogEquation

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Restriction of the actual joint Hessian to the spatial directions. -/
theorem spatialDD_apply_eq_joint {n : ℕ} {P : Point n → ℝ} {p : Point n}
    (hP : ContDiffAt ℝ 2 P p) (i j : Yau.RIdx n) :
    spatialDD P p (Yau.realVec i) (Yau.realVec j) =
      fderiv ℝ (fderiv ℝ P) p (Yau.realVec i,0) (Yau.realVec j,0) := by
  have hslice : ContDiffAt ℝ 2 (fun x => P (x,p.2)) p.1 :=
    hP.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hd : DifferentiableAt ℝ (fun z => fderiv ℝ P z (Yau.realVec j,0)) p :=
    ((hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const (Yau.realVec j,0))
  have heq : (fun x => d (fun y => P (y,p.2)) x j) =ᶠ[𝓝 p.1]
      fun x => fderiv ℝ P (x,p.2) (Yau.realVec j,0) := by
    have hgP : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ P z :=
      (hP.eventually (by norm_num)).mono (fun z hz => hz.differentiableAt (by norm_num))
    have hmap : Tendsto (fun x : Space n => (x,p.2)) (𝓝 p.1) (𝓝 p) :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hg := hmap.eventually hgP
    filter_upwards [hg] with x hx
    exact L16Aux.d_eq_joint_fderiv hx j
  have hh := congrArg (fun L : Space n →L[ℝ] ℝ => L (Yau.realVec i)) heq.fderiv_eq
  change d (fun x => d (fun y => P (y,p.2)) x j) p.1 i =
    d (fun x => fderiv ℝ P (x,p.2) (Yau.realVec j,0)) p.1 i at hh
  rw [d_d hslice,L16Aux.d_eq_joint_fderiv hd i] at hh
  change spatialDD P p (Yau.realVec i) (Yau.realVec j) = _ at hh
  rw [hh]
  simpa only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] using
    congrArg (fun L : Point n →L[ℝ] ℝ => L (Yau.realVec i,0))
      (((hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply
        (hasFDerivAt_const (Yau.realVec j,0) p)).fderiv

theorem fixed_spatial_jet_bounds {n : ℕ} {P : Point n → ℝ} {p : Point n}
    (hP : ContDiffAt ℝ 2 P p) {P₁ P₂ : ℝ}
    (h₁ : ‖fderiv ℝ P p‖ ≤ P₁) (h₂ : ‖fderiv ℝ (fderiv ℝ P) p‖ ≤ P₂) :
    (∀ i, |spatialD P p (Yau.realVec i)| ≤ P₁) ∧
      ∀ i j, |spatialDD P p (Yau.realVec i) (Yau.realVec j)| ≤ P₂ := by
  have he (i : Yau.RIdx n) : ‖(Yau.realVec i,(0 : ℝ))‖ = 1 := by
    simp [Prod.norm_def,L16Aux.realVec_norm]
  constructor
  · intro i
    change |d (fun x => P (x,p.2)) p.1 i| ≤ P₁
    rw [L16Aux.d_eq_joint_fderiv (hP.differentiableAt (by norm_num)) i]
    have hh : |fderiv ℝ P p (Yau.realVec i,0)| ≤ ‖fderiv ℝ P p‖ := by
      simpa only [Real.norm_eq_abs,he,mul_one] using (fderiv ℝ P p).le_opNorm (Yau.realVec i,0)
    exact hh.trans h₁
  · intro i j
    rw [spatialDD_apply_eq_joint hP]
    have h := ((fderiv ℝ (fderiv ℝ P) p (Yau.realVec i,0)).le_opNorm (Yau.realVec j,0)).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ P) p).le_opNorm (Yau.realVec i,0)) (norm_nonneg _))
    have hh : |fderiv ℝ (fderiv ℝ P) p (Yau.realVec i,0) (Yau.realVec j,0)| ≤
        ‖fderiv ℝ (fderiv ℝ P) p‖ := by
      simpa only [Real.norm_eq_abs,he,mul_one] using h
    exact hh.trans h₂

end Yau.LeafProofs.L16ExpBoundaryAux
