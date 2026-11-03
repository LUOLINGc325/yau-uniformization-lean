import Yau.Proofs.C05HessianPropagationJets
import Yau.Proofs.C05InverseEnergyNaturalityAlgebra
import Yau.Proofs.C05RealRicciPositive
import Yau.LeafProofs.L23RicciNaturality

/-! The actual inverse Ricci energy in a fixed chart agrees with its
global re-centered definition. No chart is varied with time. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def realDifferentialInChart (f : M.Carrier → ℝ) (c : M.Carrier)
    (z : ComplexVector n) : RIdx n → ℝ := fun a => rDeriv (inChart c f) z a

theorem scalarJet_one_evaluation (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z V : ComplexVector n) :
    tensorEvalCLM (scalarJet k f c 1 z) (fun _ : Fin 1 => V) = fderiv ℝ (inChart c f) z V := by
  let empty : Fin 0 → RIdx n := Fin.elim0
  have hvec : Fin.cons V (fun j => realVec (empty j)) = (fun _ : Fin 1 => V) := by
    funext j
    fin_cases j
    rfl
  have hcons (a : RIdx n) : Fin.cons a empty = ![a] := by funext j; fin_cases j; rfl
  rw [← hvec, tensorEvalCLM_head_basis]
  simp_rw [hcons, scalarJet_one]
  conv_rhs => rw [← sum_realCoord_realVec V]
  simp only [map_sum, map_smul, smul_eq_mul, rDeriv]

theorem realDifferentialInChart_change (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    realDifferentialInChart f c z = (realChartJacobian c d z)ᵀ *ᵥ
      realDifferentialInChart f d (realChartChange c d z) := by
  have hn := Yau.Proofs.C05HessianPropagationAux.scalarJet_eval_chart_change k hk f hf 1 c d hz hy
  funext a
  have he := congrArg (fun T : RealTensorForm n 1 => T (fun _ : Fin 1 => realVec a)) hn
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
  rw [scalarJet_one_evaluation, scalarJet_one_evaluation] at he
  change fderiv ℝ (inChart c f) z (realVec a) =
    ∑ b, realChartJacobian c d z b a *
      fderiv ℝ (inChart d f) (realChartChange c d z) (realVec b)
  rw [he]
  have hh := congrArg (fun w => fderiv ℝ (inChart d f) (realChartChange c d z) w)
    (sum_realCoord_realVec (fderiv ℝ (realChartChange c d) z (realVec a)))
  simpa only [map_sum, map_smul, smul_eq_mul, realChartJacobian, realLinearMatrix] using hh.symm

def ricciInverseEnergyInChart (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) : ℝ :=
  (1 / 2 : ℝ) * (realDifferentialInChart f c z ⬝ᵥ
    ((Matrix.of (realRicciCoeff k c z))⁻¹ *ᵥ realDifferentialInChart f c z))

theorem realRicciMatrix_chart_change (k : HermitianField M) (hk : MetricSmooth k)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    Matrix.of (realRicciCoeff k c z) = (realChartJacobian c d z)ᵀ *
      Matrix.of (realRicciCoeff k d (realChartChange c d z)) * realChartJacobian c d z := by
  ext a b
  rw [Matrix.of_apply, realRicciCoeff_chart_change k hk c d hz hy]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem ricciInverseEnergyInChart_change (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    ricciInverseEnergyInChart k f c z =
      ricciInverseEnergyInChart k f d (realChartChange c d z) := by
  have hJ : (realChartJacobian c d z).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse (realChartJacobian_left_inverse c d hz hy)
  unfold ricciInverseEnergyInChart
  rw [realRicciMatrix_chart_change k hk c d hz hy, realDifferentialInChart_change k hk f hf c d hz hy]
  exact congrArg (fun q : ℝ => (1 / 2 : ℝ) * q) (inverseMatrixEnergy_congruence _ _ hJ _)

theorem ricciInverseEnergyInChart_center (k : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) : ricciInverseEnergyInChart k f x (chartPt x x) =
      realRicciDifferentialEnergy k f x := by
  unfold ricciInverseEnergyInChart realRicciDifferentialEnergy realDifferentialInChart
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem ricciInverseEnergyInChart_eq_global (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    ricciInverseEnergyInChart k f c z = realRicciDifferentialEnergy k f (chartInv c z) := by
  have h := ricciInverseEnergyInChart_change k hk f hf c (chartInv c z) hz
    (mem_extChartAt_source (chartInv c z))
  change ricciInverseEnergyInChart k f c z =
    ricciInverseEnergyInChart k f (chartInv c z) (chartPt (chartInv c z) (chartInv c z)) at h
  exact h.trans (ricciInverseEnergyInChart_center k f _)

end Yau.Proofs.C05Aux
