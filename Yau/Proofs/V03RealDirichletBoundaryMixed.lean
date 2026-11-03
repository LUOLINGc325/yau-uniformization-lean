import Yau.Proofs.V03RealParameterMixedJet
import Yau.Proofs.V03DirichletScaling

/-! The mixed seminorm estimate uses the boundary seminorm of the actual
pointwise mixed derivative, with exact normalization. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem scalarDSq_parameterLaplacian {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ × ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (U ×ˢ Set.univ))
    (h0 : (0 : ℂ) ∈ U) :
    boundaryDSq (fun θ (_ : Unit) => realParameterLaplacian (fun p => (g p : ℂ)) (0, θ)) =
      ENNReal.ofReal 16 * scalarDSq (fun θ => mixedReal (fun z => g (z, θ))) := by
  have he : (fun θ (_ : Unit) => realParameterLaplacian (fun p => (g p : ℂ)) (0, θ)) =
      (fun θ (_ : Unit) => (4 : ℂ) * (mixedReal (fun z => g (z, θ)) : ℂ)) := by
    funext θ _
    exact realParameterLaplacian_ofReal_eq_four_mixed hU hg h0 θ
  rw [he, boundaryDSq_const_mul]
  norm_num [scalarDSq]

theorem abs_mixedReal_scalarDSq_le_actual_mixed {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ × ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => g (z, θ)) (2 * Real.pi))
    (h0 : (0 : ℂ) ∈ U) :
    |mixedReal (fun z => (scalarDSq (fun θ => g (z, θ))).toReal)| ≤
      (1 / 2 : ℝ) * ((boundaryDSq (fun θ (_ : Unit) =>
        realParameterDerivative (fun p => (g p : ℂ)) 1 (0, θ))).toReal +
        (boundaryDSq (fun θ (_ : Unit) =>
          realParameterDerivative (fun p => (g p : ℂ)) Complex.I (0, θ))).toReal) +
      2 * Real.sqrt (scalarDSq (fun θ => g (0, θ))).toReal *
        Real.sqrt (scalarDSq (fun θ => mixedReal (fun z => g (z, θ)))).toReal := by
  have hb := abs_mixedReal_boundaryDSq_le_actual_jets hU hg hp h0
  dsimp only at hb
  rw [scalarDSq_parameterLaplacian hU hg h0, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 16),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)] at hb
  norm_num at hb
  exact hb.trans_eq (by unfold scalarDSq; ring)

end Yau.Blueprint.V03Proof
