import Yau.LeafProofs.L21LeviHermitian
import Yau.LeafProofs.L21BoundaryWeight
import Yau.LeafProofs.L21RealCoordinates

/-! The corrected Levi expression is the true real Hessian contraction
plus an explicit first-order coefficient error. -/

open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def leviFirstCoefficient (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Fin n → Fin n → X n → ℂ) (i j : Fin n) (b : Yau.RIdx n) (x : X n) : ℂ :=
  (∑ a : Yau.RIdx n, dbarRealCoefficient A i a x *
    fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x (Yau.realVec a)) -
      ∑ k, d i j k x * star (dbarRealCoefficient A k b x)

def leviHessianPart (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (φ : X n → ℝ) (i j : Fin n) (x : X n) : ℂ :=
  ∑ a : Yau.RIdx n, ∑ b : Yau.RIdx n,
    dbarRealCoefficient A i a x * star (dbarRealCoefficient A j b x) *
      fderiv ℝ (fderiv ℝ (fun y => (φ y : ℂ))) x (Yau.realVec a) (Yau.realVec b)

theorem correctedLevi_hessian_decomposition {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    (d : Fin n → Fin n → Fin n → X n → ℂ) (i j : Fin n) {x : X n} (hx : x ∈ O) :
    correctedLevi A φ d i j x = leviHessianPart A φ i j x +
      ∑ b : Yau.RIdx n, leviFirstCoefficient A d i j b x *
        fderiv ℝ (fun y => (φ y : ℂ)) x (Yau.realVec b) := by
  have hp (b : Yau.RIdx n) : DifferentiableAt ℝ
      (fun y => star (dbarRealCoefficient A j b y)) x :=
    (((dbarRealCoefficient_smoothOn hA j b).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)).star
  have hf := (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ).contDiffAt (hO.mem_nhds hx)
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hFirst : (∑ a : Yau.RIdx n, ∑ b : Yau.RIdx n,
      dbarRealCoefficient A i a x * fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x
        (Yau.realVec a) * fderiv ℝ (fun y => (φ y : ℂ)) x (Yau.realVec b)) =
      ∑ b : Yau.RIdx n, (∑ a : Yau.RIdx n,
        dbarRealCoefficient A i a x * fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x
          (Yau.realVec a)) * fderiv ℝ (fun y => (φ y : ℂ)) x (Yau.realVec b) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  have hLower : (∑ k, d i j k x * conjugateD A k (fun y => (φ y : ℂ)) x) =
      ∑ b : Yau.RIdx n, (∑ k, d i j k x * star (dbarRealCoefficient A k b x)) *
        fderiv ℝ (fun y => (φ y : ℂ)) x (Yau.realVec b) := by
    simp only [conjugateD, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hExpand : dbarA A i (conjugateD A j (fun y => (φ y : ℂ))) x =
      leviHessianPart A φ i j x +
        ∑ b : Yau.RIdx n, (∑ a : Yau.RIdx n,
          dbarRealCoefficient A i a x * fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x
            (Yau.realVec a)) * fderiv ℝ (fun y => (φ y : ℂ)) x (Yau.realVec b) := by
    rw [dbarA_eq_real_rows]
    change (∑ a : Yau.RIdx n, dbarRealCoefficient A i a x *
      fderiv ℝ (rowApply Yau.realVec (fun b y => star (dbarRealCoefficient A j b y))
        (fun y => (φ y : ℂ))) x (Yau.realVec a)) = _
    simp only [fderiv_rowApply (f := fun y => (φ y : ℂ)) Yau.realVec _ hp hdf, Finset.mul_sum, mul_add,
      Finset.sum_add_distrib]
    have hTerms : (∑ a : Yau.RIdx n, ∑ b : Yau.RIdx n,
        dbarRealCoefficient A i a x *
          (fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x (Yau.realVec a) *
            fderiv ℝ (fun y => (φ y : ℂ)) x (Yau.realVec b))) =
        ∑ a : Yau.RIdx n, ∑ b : Yau.RIdx n,
          dbarRealCoefficient A i a x * fderiv ℝ (fun y => star (dbarRealCoefficient A j b y)) x
            (Yau.realVec a) * fderiv ℝ (fun y => (φ y : ℂ)) x (Yau.realVec b) := by
      simp only [mul_assoc]
    rw [hTerms, hFirst]
    dsimp only [leviHessianPart]
    simp only [mul_assoc]
    ring
  unfold correctedLevi
  rw [hExpand, hLower]
  simp only [leviFirstCoefficient, sub_mul, Finset.sum_sub_distrib]
  ring

theorem realVec_inner (a b : Yau.RIdx n) :
    inner ℝ (Yau.realVec a) (Yau.realVec b) = if a = b then 1 else 0 := by
  rw [← realBasis_apply n a, ← realBasis_apply n b]
  exact (realBasis n).inner_eq_ite a b

theorem second_boundaryWeight_ofReal {K : ℝ} {x : X n}
    (hx : x ∈ Metric.ball (0 : X n) 1) (a b : Yau.RIdx n) :
    fderiv ℝ (fderiv ℝ (fun y : X n => (boundaryWeight K y : ℂ))) x
      (Yau.realVec a) (Yau.realVec b) =
        (2 * K * (rho x)⁻¹ ^ 2 * (if a = b then 1 else 0) +
          8 * K * (rho x)⁻¹ ^ 3 * inner ℝ x (Yau.realVec a) * inner ℝ x (Yau.realVec b) : ℝ) := by
  have hφ := (contDiffOn_boundaryWeight K).contDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have hdf := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hDC : (fun y : X n => fderiv ℝ (fun z : X n => (boundaryWeight K z : ℂ)) y (Yau.realVec b)) =ᶠ[𝓝 x]
      (fun y : X n => (fderiv ℝ (boundaryWeight K : X n → ℝ) y (Yau.realVec b) : ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact fderiv_ofReal_apply (((contDiffOn_boundaryWeight K).contDiffAt
      (Metric.isOpen_ball.mem_nhds hy)).differentiableAt (by simp)) _
  have hCdf : DifferentiableAt ℝ (fderiv ℝ (fun y : X n => (boundaryWeight K y : ℂ))) x :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffAt x hφ).fderiv_right (m := ∞)
      (by simp)).differentiableAt (by simp)
  rw [← fderiv_directional hCdf, hDC.fderiv_eq,
    fderiv_ofReal_apply (hdf.clm_apply (differentiableAt_const _)),
    second_fderiv_boundaryWeight K hx, realVec_inner]
  simp only [eq_comm]
  congr 1
  ring

end Yau.LeafProofs.L21Aux
