import Yau.LeafProofs.L10DiscEnergyComplex
import Yau.LeafProofs.L10Tensor

/-! The original Fréchet tensor norms are controlled by the coordinate energies. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

theorem discEnergyPartial_twice_eq_tensor {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) (v w : ℂ) :
    discEnergyPartial (discEnergyPartial u v) w z =
      iteratedFDeriv ℝ 2 u z ![w, v] := by
  have hD : DifferentiableAt ℝ (fderiv ℝ u) z :=
    ((discEnergy_contDiffAt hu hz).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [discEnergyPartial_twice_eq u v w hz, fderiv_clm_apply hD (differentiableAt_const v)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ContinuousLinearMap.flip_apply, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add]

theorem discEnergy_tensor_one_le {u : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖iteratedFDeriv ℝ 1 u z‖^2 ≤ discEnergyGradientSq u z := by
  classical
  have h := multilinear_norm_sq_le_basis_energy Complex.orthonormalBasisOneI
    (iteratedFDeriv ℝ 1 u z)
  have hsum : (∑ w : Fin 1 → Fin 2,
      ‖iteratedFDeriv ℝ 1 u z (fun j => Complex.orthonormalBasisOneI (w j))‖^2) =
      ∑ i : Fin 2, ‖fderiv ℝ u z (Complex.orthonormalBasisOneI i)‖^2 := by
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2))
    intro w
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [hsum] at h
  simpa only [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, discEnergyGradientSq,
    discEnergyPartial_eq_fderiv u _ hz] using h

theorem discEnergy_tensor_two_le {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖iteratedFDeriv ℝ 2 u z‖^2 ≤ discEnergyHessianSq u z := by
  classical
  have h := multilinear_norm_sq_le_basis_energy Complex.orthonormalBasisOneI
    (iteratedFDeriv ℝ 2 u z)
  have hsum : (∑ w : Fin 2 → Fin 2,
      ‖iteratedFDeriv ℝ 2 u z (fun j => Complex.orthonormalBasisOneI (w j))‖^2) =
      ∑ p : Fin 2 × Fin 2,
        ‖discEnergyPartial (discEnergyPartial u (Complex.orthonormalBasisOneI p.2))
          (Complex.orthonormalBasisOneI p.1) z‖^2 := by
    apply Fintype.sum_equiv (finTwoArrowEquiv (Fin 2))
    intro w
    rw [discEnergyPartial_twice_eq_tensor hu hz]
    congr 2
    apply congrArg (iteratedFDeriv ℝ 2 u z)
    funext j
    fin_cases j <;> rfl
  rw [hsum, Fintype.sum_prod_type] at h
  simp only [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  unfold discEnergyHessianSq
  linarith only [h]

theorem discEnergyHessianSq_continuousOn {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discEnergyHessianSq u) (Metric.closedBall (0 : ℂ) 1) := by
  have hc (v w : ℂ) : ContinuousOn (fun z => ‖discEnergyPartial (discEnergyPartial u v) w z‖^2)
      (Metric.closedBall (0 : ℂ) 1) :=
    ((discEnergyPartial_contDiffOn (discEnergyPartial_contDiffOn hu v) w).continuousOn.norm.pow 2)
  exact (((hc 1 1).add (hc 1 Complex.I)).add (hc Complex.I 1)).add (hc Complex.I Complex.I)

theorem discEnergy_iterated_integrable {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) (k : ℕ) :
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ k u z‖^2) (Metric.ball (0 : ℂ) 1) := by
  have hc := hu.continuousOn_iteratedFDerivWithin
    (m := k) (by exact_mod_cast (ENat.natCast_lt_top k).le) disc_closedBall_uniqueDiffOn
  apply (discEnergy_integrableOn (hc.norm.pow 2)).congr_fun ?_ Metric.isOpen_ball.measurableSet
  intro z hz
  dsimp only [Pi.pow_apply]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv disc_closedBall_uniqueDiffOn
    ((discEnergy_contDiffAt hu hz).of_le (by exact_mod_cast (ENat.natCast_lt_top k).le))
    (Metric.ball_subset_closedBall hz)]

theorem discEnergy_original_norm_le {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    (∑ k ∈ Finset.range 3, ∫ z in Metric.ball (0 : ℂ) 1, ‖iteratedFDeriv ℝ k u z‖^2) ≤
      (∫ z in Metric.ball (0 : ℂ) 1, ‖u z‖^2) +
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyGradientSq u z) +
      ∫ z in Metric.ball (0 : ℂ) 1, discEnergyHessianSq u z := by
  have h1 := integral_mono_ae (discEnergy_iterated_integrable hu 1)
    (discEnergy_integrableOn (discEnergyGradientSq_continuousOn hu)) (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      exact discEnergy_tensor_one_le hz)
  have h2 := integral_mono_ae (discEnergy_iterated_integrable hu 2)
    (discEnergy_integrableOn (discEnergyHessianSq_continuousOn hu)) (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
      exact discEnergy_tensor_two_le hu hz)
  simp only [show 3 = 2+1 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, norm_iteratedFDeriv_zero]
  linarith only [h1, h2]

end Yau.LeafProofs
