import Yau.Proofs.F05RoughCoefficientBudget
import Yau.Proofs.F05ExponentialHolder

/-! A value Hölder bound alone gives uniform genuine nonlinear principal
and drift coefficient budgets. No derivative of the candidate occurs. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_value_nonlinear_coefficient_budgets {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {S D : ℝ}
    (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S)) (hD : 0 ≤ D) :
    ∃ lam upper C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 →
      ∀ T : ℝ, T ≤ S → ∀ w : M.Carrier → ℝ → ℝ,
      (∀ i, HolderBound α (F05Q A i T) (pull A i w) D) →
      ∀ i, Elliptic (F05Q A i T)
          (F05FlowPrincipal A i h (fun x t => Real.exp (-w x t))) lam upper ∧
        HolderBound α (F05Q A i T)
          (F05FlowPrincipal A i h (fun x t => Real.exp (-w x t))) C ∧
        ∀ j, HolderBound α (F05Q A i T)
          (fun z => F05FlowDrift A i h (fun x t => Real.exp (-w x t)) z j) C := by
  let E := Real.exp D*(1+D)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hRange : Real.exp (-D) ≤ Real.exp D := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨lam,upper,C,hC,hBudget⟩ := F05_rough_scalar_coefficient_budgets hA h hS hh hE
    (Real.exp_pos (-D)) hRange
  refine ⟨lam,upper,C,hC,?_⟩
  intro α hα hα1 T hTS w hw
  apply hBudget α hα hα1 T hTS (fun x t => Real.exp (-w x t))
  · intro i
    exact F05_holder_exp (holderBound_neg (hw i)) (fun z hz =>
      (neg_le_abs (pull A i w z)).trans ((hw i).2.1 z hz))
  · intro i z hz
    have hAbs : |pull A i w z| ≤ D := by
      simpa only [Real.norm_eq_abs] using (hw i).2.1 z hz
    change Real.exp (-D) ≤ Real.exp (-pull A i w z) ∧ Real.exp (-pull A i w z) ≤ Real.exp D
    exact ⟨Real.exp_le_exp.mpr (by linarith [(le_abs_self (pull A i w z))]),
      Real.exp_le_exp.mpr ((neg_le_abs _).trans hAbs)⟩

end Yau.Proofs.F05Aux
