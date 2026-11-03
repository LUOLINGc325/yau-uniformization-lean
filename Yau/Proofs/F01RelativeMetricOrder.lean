import Yau.Proofs.F01MatrixSandwichMono

/-! Any two actual positive Hermitian matrices admit a finite relative
upper comparison, with no extra geometric or spectral hypothesis. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_relative_metric_upper_order {H K : Matrix ι ι ℂ}
    (hH : H.PosDef) (hK : K.PosDef) :
    ∃ C : ℝ, 0 < C ∧ ((C : ℂ) • H - K).PosSemidef := by
  obtain ⟨D, hD, hbH⟩ := compact_posDef_matrix_sandwich
    (G := fun _ : Unit => H) (K := {()}) isCompact_singleton
    continuous_const.continuousOn (fun _ _ => hH)
  obtain ⟨E, hE, hbK⟩ := compact_posDef_matrix_sandwich
    (G := fun _ : Unit => K) (K := {()}) isCompact_singleton
    continuous_const.continuousOn (fun _ _ => hK)
  have hHlo := (hbH () (by simp)).1
  have hKhi := (hbK () (by simp)).2
  have hscaled := hHlo.smul (mul_nonneg hD.le hE.le)
  have hsum := hscaled.add hKhi
  refine ⟨D * E, mul_pos hD hE, ?_⟩
  convert! hsum using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.real_smul]
  have hd : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  field_simp [hd]
  <;> ring

end Yau.NodeProofs.F01Aux
