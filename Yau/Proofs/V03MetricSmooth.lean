import Yau.Proofs.V03DualNorm

/-! Entrywise smooth inverse metric and the actual dual norm calculator
in each valid fixed cotangent chart. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem entrywise_matrix_det_contDiffOn {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]
    {A : E → Matrix ι ι ℂ} {S : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) S) :
    ContDiffOn ℝ ∞ (fun z => (A z).det) S := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

theorem entrywise_matrix_inv_contDiffOn {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]
    {A : E → Matrix ι ι ℂ} {S : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) S)
    (hdet : ∀ z ∈ S, (A z).det ≠ 0) (i j : ι) :
    ContDiffOn ℝ ∞ (fun z => (A z)⁻¹ i j) S := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_apply]
  apply ((entrywise_matrix_det_contDiffOn hA).inv hdet).mul
  apply entrywise_matrix_det_contDiffOn
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact contDiffOn_const
  · simp only [hkj, ↓reduceIte]
    exact hA k l

variable {n : ℕ} {M : ComplexManifold n}

theorem hMat_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => hMat g.form x z i j) (chartTarget x) :=
  g.coordinate_smooth x i j

theorem hMat_inverse_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => (hMat g.form x z)⁻¹ i j) (chartTarget x) :=
  entrywise_matrix_inv_contDiffOn (hMat_contDiffOn g x)
    (fun z hz => ne_of_gt (hMat_posDef g.form x z hz).det_pos) i j

theorem dualNormChart_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n => dualNormChart g.form x p.1 p.2)
      (cotangentTarget x) := by
  have hξ (i : Fin n) : ContDiffOn ℝ ∞ (fun p : CotangentCoord n => p.2 i)
      (cotangentTarget x) :=
    ((contDiff_piLp_apply (p := 2) (i := i)).comp contDiff_snd).contDiffOn
  have hinv (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : CotangentCoord n => (hMat g.form x p.1)⁻¹ i j) (cotangentTarget x) :=
    (hMat_inverse_contDiffOn g x i j).comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  have hC : ContDiffOn ℝ ∞ (fun p : CotangentCoord n =>
      ∑ i, star (p.2 i) * ∑ j, (hMat g.form x p.1)⁻¹ j i * p.2 j)
      (cotangentTarget x) :=
    ContDiffOn.sum fun i _ => (Complex.conjCLE.contDiff.comp_contDiffOn (hξ i)).mul
      (ContDiffOn.sum fun j _ => (hinv j i).mul (hξ j))
  exact Complex.reCLM.contDiff.comp_contDiffOn hC

end Yau.Blueprint.V03Proof
