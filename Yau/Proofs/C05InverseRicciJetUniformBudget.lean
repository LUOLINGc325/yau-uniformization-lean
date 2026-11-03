import Yau.Proofs.C05InverseRicciJetUniformBudgetConstants
import Yau.Proofs.C05MetricInverseBound
import Yau.Proofs.C05QJetBudgetInverse
import Yau.Proofs.C05RicciInverseEnergyRegularity
import Yau.Proofs.C05RealRicciJets
import Mathlib.Tactic.IntervalCases

/-! A pointwise coercivity and true Ricci-jet bound give one uniform inverse-jet budget. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05InverseRicciJetUniformBudgetAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05QJetBudgetAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem inverseRicciJet_norm_le_budget (μ B : ℝ) (hμ : 0 < μ) (hB : 0 ≤ B)
    (k : HermitianField M) (hk : MetricSmooth k) (hK : KahlerClosed k)
    (hRic : ∀ y, (ricci k y).PosDef) (x : M.Carrier)
    (hcoercive : ∀ v : RIdx n → ℝ,
      μ * (v ⬝ᵥ (realMetricFn k x (chartPt x x) *ᵥ v)) ≤
        v ⬝ᵥ (Matrix.of (realRicciCoeff k x (chartPt x x)) *ᵥ v))
    (hR : ∀ j ≤ 3, realRicciJetNorm k j x ≤ B) :
    ∀ j ≤ 3, metricTensorNorm (realMetricFn k x (chartPt x x))
      (inverseFieldJet k x (fun z => Matrix.of (realRicciCoeff k x z)) j (chartPt x x)) ≤
        inverseRicciJetBudget n μ B := by
  let G := realMetricFn k x (chartPt x x)
  let A := fun z => Matrix.of (realRicciCoeff k x z)
  let N := fun j => metricTensorNorm G (inverseFieldJet k x A j (chartPt x x))
  let R := fun j => realRicciJetNorm k j x
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hG : G.PosDef := realMetricFn_posDef k x _ hz
  have hA (a b : RIdx n) : ContDiffOn ℝ ∞ (fun z => A z a b) (chartTarget x) :=
    realRicciCoeff_contDiffOn k hk x a b
  have hdet (z) (hz : z ∈ chartTarget x) : (A z).det ≠ 0 :=
    (realRicciMatrix_posDef_inChart k hk hK hRic x hz).det_pos.ne'
  have hN (j : ℕ) : 0 ≤ N j := metricTensorNorm_nonneg _ _
  have hRn (j : ℕ) : 0 ≤ R j := Real.sqrt_nonneg _
  have h0 : N 0 ≤ coefficientZero n μ := by
    have H := loweredInverseMatrix_metric_normSq_bound G (A (chartPt x x)) hG
      (hdet _ hz) μ hμ hcoercive
    have hs : N 0 ^ 2 = covTensorNormSq G
        (matrixCovTensor (loweredInverseMatrix G (A (chartPt x x)))) :=
      Real.sq_sqrt (covTensorNormSq_nonneg G hG _)
    have hb : (N 0 * μ) ^ 2 ≤ (Real.sqrt (2*n:ℕ)) ^ 2 := by
      calc
        _ = μ ^ 2 * N 0 ^ 2 := by ring
        _ ≤ (2*n:ℕ) := by rw [hs]; exact H
        _ = _ := (Real.sq_sqrt (Nat.cast_nonneg (2*n) : (0:ℝ)≤(2*n:ℕ))).symm
    change N 0 ≤ Real.sqrt (2*n:ℕ) / μ
    exact (le_div_iff₀ hμ).mpr
      ((sq_le_sq₀ (mul_nonneg (hN 0) hμ.le) (Real.sqrt_nonneg _)).mp hb)
  have he1 := inverseFieldJet_one_norm_le k hk x A hz
    (fun a b => ((hA a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp))
    (hdet _ hz)
  change N 1 ≤ (2*n:ℕ) * N 0 ^ 2 * R 1 at he1
  have he2 := inverseFieldJet_two_norm_le k hk x A hA hdet hz
  change N 2 ≤ (2*n:ℕ) * (2*N 0*N 1) * R 1 + (2*n:ℕ) * N 0 ^ 2 * R 2 at he2
  have he3 := inverseFieldJet_three_norm_le k hk x A hA hdet hz
  change N 3 ≤ (2*n:ℕ) * ((2*N 0*N 2+2*N 1 ^ 2)*R 1+
    4*N 0*N 1*R 2+N 0 ^ 2*R 3) at he3
  obtain ⟨h1,h2,h3⟩ := polynomial_majorants n hμ hB (hN 0) (hN 1) (hN 2)
    (hRn 1) (hRn 2) (hRn 3) h0 (hR 1 (by omega)) (hR 2 (by omega)) (hR 3 (by omega))
    he1 he2 he3
  obtain ⟨hC0,hC1,hC2,hC3⟩ := coefficients_nonneg n hμ hB
  intro j hj
  change N j ≤ inverseRicciJetBudget n μ B
  unfold inverseRicciJetBudget
  interval_cases j <;> linarith

theorem exists_uniform_inverseRicciJet_bound (n : ℕ) (μ B : ℝ)
    (hμ : 0 < μ) (hB : 0 ≤ B) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ (M : ComplexManifold n) (k : HermitianField M)
      (hk : MetricSmooth k) (hK : KahlerClosed k) (hRic : ∀ y, (ricci k y).PosDef)
      (x : M.Carrier),
      (∀ v : RIdx n → ℝ, μ * (v ⬝ᵥ (realMetricFn k x (chartPt x x) *ᵥ v)) ≤
        v ⬝ᵥ (Matrix.of (realRicciCoeff k x (chartPt x x)) *ᵥ v)) →
      (∀ j ≤ 3, realRicciJetNorm k j x ≤ B) →
      ∀ j ≤ 3, metricTensorNorm (realMetricFn k x (chartPt x x))
        (inverseFieldJet k x (fun z => Matrix.of (realRicciCoeff k x z)) j (chartPt x x)) ≤ CA := by
  refine ⟨inverseRicciJetBudget n μ B,inverseRicciJetBudget_pos n hμ hB,?_⟩
  intro M k hk hK hRic x hcoercive hR
  exact inverseRicciJet_norm_le_budget μ B hμ hB k hk hK hRic x hcoercive hR

end Yau.Proofs.C05InverseRicciJetUniformBudgetAux
