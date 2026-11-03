import Yau.Proofs.C01MovingRicciHarnack

/-! The moving-frame matrix of the original flow is an actual smooth
real continuous linear ODE coefficient on positive time. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

def matrixRealCLM (A : Herm n) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  A.mulVecLin.toContinuousLinearMap.restrictScalars ℝ

theorem matrixRealCLM_apply (A : Herm n) (v : Fin n → ℂ) :
    matrixRealCLM A v = A *ᵥ v := rfl

def movingFrameCoefficient (h : Flow X) (x : Pt X) (t : ℝ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  matrixRealCLM (movingFrameMatrix h x t)

theorem localizedFlow_movingFrameMatrix_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => movingFrameMatrix h x t i j) (Set.Ioi 0) := by
  have hmetric (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun t => gMat (h t) x a b) (Set.Ioi 0) :=
    (localizedFlow_gMat_time_contDiffOn hflow x a b).mono Set.Ioi_subset_Ici_self
  have hdet (t : ℝ) (ht : t ∈ Set.Ioi 0) : (gMat (h t) x).det ≠ 0 :=
    ((Alignment.Y03Proof.hMat_posDef (h t) x (chartPt x x)
      (mem_extChartAt_target (I := ComplexModel n) x)).isUnit.map Matrix.detMonoidHom).ne_zero
  have hinv (a b : Fin n) :=
    Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_inv hmetric hdet a b
  simp only [movingFrameMatrix, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  exact contDiffOn_const.mul (ContDiffOn.sum fun p _ =>
    (hinv i p).mul (localizedFlow_ricci_time_contDiffOn hflow x p j))

theorem localizedFlow_movingFrameCoefficient_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) :
    ContDiffOn ℝ 2 (movingFrameCoefficient h x) (Set.Ioi 0) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_pi.mpr
  intro i
  change ContDiffOn ℝ 2 (fun t => ∑ j, movingFrameMatrix h x t i j * v j) (Set.Ioi 0)
  exact ContDiffOn.sum fun j _ =>
    ((localizedFlow_movingFrameMatrix_contDiffOn hflow x i j).of_le (by simp)).mul contDiffOn_const

end Yau.NodeProofs.C01Aux
