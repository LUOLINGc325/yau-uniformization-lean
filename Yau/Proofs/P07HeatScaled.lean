import Yau.Proofs.P07HeatComplement
import Yau.Proofs.P07HeatTranslates
import Yau.Proofs.P07MatrixOrder

/-! The same actual heat slice has a uniform scaled gradient and two-sided
Levi bound from the original upper estimate and its derived lower trace. -/
noncomputable section
open Set
open scoped Topology ComplexOrder
namespace Yau.NodeProofs.P07Aux
open Yau Yau.Blueprint Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux
variable {n : ℕ}

theorem continuousInitialHeat_scaled_derivatives (X : KahlerManifold n)
    (f : Pt X → ℝ) (U : ℝ → Pt X → ℝ)
    (hU : IsContinuousInitialScalarHeat X.metric.form f U)
    (h01 : ∀ x t, 0 < t → U t x ∈ Icc (0 : ℝ) 1)
    {A ε L : ℝ} (hA : 0 < A) (hε : 0 < ε) (hL : 0 < L)
    (hupper : ∀ x, HermLE (levi (U (ε * L ^ 2)) x)
      (((A / L ^ 2 : ℝ) : ℂ) • gMat X.metric.form x)) :
    (∀ x, gradNormSq X.metric.form (U (ε * L ^ 2)) x ≤ (12 * (n : ℝ) / ε) / L ^ 2) ∧
    (∀ x v, |leviDirection (levi (U (ε * L ^ 2)) x) v| ≤
      ((((n : ℝ) + 1) * A + 2 * (n : ℝ) / ε) / L ^ 2) *
        leviDirection (gMat X.metric.form x) v) := by
  have ht : 0 < ε * L ^ 2 := mul_pos hε (sq_pos_of_pos hL)
  have hder (x) := continuousInitialHeat_derivative_bounds X
    (P06Aux.kahlerManifold_ricci_posSemidef X) f U hU h01 x ht
  have hgradEq : 12 * (n : ℝ) / (ε * L ^ 2) = (12 * (n : ℝ) / ε) / L ^ 2 := by field_simp
  constructor
  · intro x
    simpa only [hgradEq] using (hder x).2
  · intro x v
    have htrace : -(2 * (n : ℝ) / (ε * L ^ 2)) ≤
        traceWith (gMat X.metric.form x) (levi (U (ε * L ^ 2)) x) := (abs_le.mp (hder x).1).1
    have hh := relative_abs_directional_of_upper_and_trace
      (gMat X.metric.form x) (levi (U (ε * L ^ 2)) x)
      (Yau.LeafProofs.L12Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x))
      (G04Aux.levi_hermitian _ (smoothSpaceTime_slice hU.2.1 ht) x)
      (a := A / L ^ 2) (b := 2 * (n : ℝ) / (ε * L ^ 2)) (by positivity) (by positivity)
      (hupper x) htrace v
    have he : ((n : ℝ) + 1) * (A / L ^ 2) + 2 * (n : ℝ) / (ε * L ^ 2) =
        (((n : ℝ) + 1) * A + 2 * (n : ℝ) / ε) / L ^ 2 := by field_simp
    simpa only [he] using hh

end Yau.NodeProofs.P07Aux
