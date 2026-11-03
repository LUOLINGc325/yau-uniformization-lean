import Mathlib

/-! Holomorphic entrywise inversion of the actual gauge matrix. -/

noncomputable section
open scoped ContDiff Matrix

namespace Yau.Proofs.C03Aux.ChernGauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_contDiffOn_complex
    {A : E → Matrix ι ι ℂ} {O : Set E}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) O) :
    ContDiffOn ℂ ∞ (fun z => (A z).det) O := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

theorem matrix_inv_contDiffOn_complex
    {A : E → Matrix ι ι ℂ} {O : Set E}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) O)
    (hdet : ∀ z ∈ O, (A z).det ≠ 0) (i j : ι) :
    ContDiffOn ℂ ∞ (fun z => (A z)⁻¹ i j) O := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((matrix_det_contDiffOn_complex hA).inv hdet).mul
  apply matrix_det_contDiffOn_complex
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact contDiffOn_const
  · simp only [hkj, ↓reduceIte]
    exact hA k l

end Yau.Proofs.C03Aux.ChernGauge
