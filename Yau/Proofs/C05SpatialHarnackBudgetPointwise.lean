import Yau.Proofs.C05InverseRicciJetUniformBudget
import Yau.Proofs.C05InverseEnergyJetBudget
import Yau.Proofs.C05ScalarTimeSourceBoundsJets
import Yau.Proofs.C05HarnackMinimumScaling
import Yau.Proofs.C05ScalarJetLinearity

/-! The actual inverse Ricci, scalar source and inverse differential energy
have one dimensional three-jet bound, without a free energy-jet certificate. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C05SpatialHarnackBudgetAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau.Proofs.C05InverseRicciJetUniformBudgetAux
open Yau.Proofs.C05InverseEnergyJetBudgetAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def spatialHarnackJetBudget (n : ℕ) (μ B K : ℝ) : ℝ :=
  1 + C05ScalarTimeSourceBoundsAux.b1 n B + K * B +
    32 * (2*n : ℕ) * inverseRicciJetBudget n μ B * B ^ 2

theorem spatialHarnackJetBudget_pos (n : ℕ) {μ B K : ℝ}
    (hμ : 0 < μ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    0 < spatialHarnackJetBudget n μ B K := by
  have h1 := C05ScalarTimeSourceBoundsAux.b1_nonneg n hB
  have hC := inverseRicciJetBudget_pos n hμ hB
  unfold spatialHarnackJetBudget
  positivity

theorem pointwise_harnack_jet_bound (g : SmoothMetric M)
    (μ B K : ℝ) (hμ : 0 < μ) (hB : 0 ≤ B) (hKcap : 0 ≤ K)
    (hRic : ∀ y, (ricci g.form y).PosDef) (κ : ℝ) (hκ : |κ| ≤ K) (x : M.Carrier)
    (hcoercive : ∀ v : RIdx n → ℝ,
      μ * (v ⬝ᵥ (realMetricFn g.form x (chartPt x x) *ᵥ v)) ≤
        v ⬝ᵥ (Matrix.of (realRicciCoeff g.form x (chartPt x x)) *ᵥ v))
    (hScalar : ∀ j ≤ 6, scalarJetNorm g.form (scalarCurvature g.form) j x ≤ B)
    (hRicci : ∀ j ≤ 4, realRicciJetNorm g.form j x ≤ B) :
    scalarJetNorm g.form (intrinsicHarnackMinimum g.form κ) 3 x ≤
      spatialHarnackJetBudget n μ B K := by
  let k := g.form
  have hk : MetricSmooth k := metricSmooth_of_smoothMetric g
  have hK : KahlerClosed k := g.kahler_equations
  let CA := inverseRicciJetBudget n μ B
  have hCA : 0 ≤ CA := (inverseRicciJetBudget_pos n hμ hB).le
  have hInv := inverseRicciJet_norm_le_budget μ B hμ hB k hk hK hRic x hcoercive
    (fun j hj => hRicci j (by omega))
  have hR : SmoothFn (scalarCurvature k) := C05Aux.scalarCurvature_smoothFn k hk hK
  have hQ : SmoothFn (realRicciDifferentialEnergy k (scalarCurvature k)) :=
    realRicciDifferentialEnergy_smoothFn k hk hK hRic _ hR
  have hEnergy := scalarJetNorm_realRicciDifferentialEnergy_le k hk hK hRic
    (scalarCurvature k) hR 3 (by omega) x hCA hB hInv (fun j hj => hScalar j (by omega))
  have hSource1 := C05ScalarTimeSourceBoundsAux.source1_jet_bound k hk hK 3 (by omega) x hB hScalar hRicci
  have hS1 : SmoothFn (scalarTimeSource1 k) := C05ScalarTimeSourceBoundsAux.source1_smoothFn k hk hK
  have hS : SmoothFn (scalarHarnackSource k κ) := scalarHarnackSource_smoothFn k hk hK κ
  have hSκ := scalarJetNorm_add_le k hk (scalarTimeSource1 k)
    (fun y => κ * scalarCurvature k y) hS1 (fun c => contDiffOn_const.mul (hR c)) 3 x
  rw [scalarJetNorm_const_mul k hk _ hR κ 3 x] at hSκ
  have hsum : (fun y => scalarTimeSource1 k y + κ * scalarCurvature k y) = scalarHarnackSource k κ := by
    rw [C05ScalarTimeSourceBoundsAux.source1_function]
    rfl
  rw [hsum] at hSκ
  have hκR : |κ| * scalarJetNorm k (scalarCurvature k) 3 x ≤ K * B :=
    mul_le_mul hκ (hScalar 3 (by omega)) (scalarJetNorm_nonneg k _ 3 x) hKcap
  have hSource : scalarJetNorm k (scalarHarnackSource k κ) 3 x ≤
      C05ScalarTimeSourceBoundsAux.b1 n B + K * B :=
    hSκ.trans (add_le_add hSource1 hκR)
  have hMin := scalarJetNorm_add_le k hk (scalarHarnackSource k κ)
    (fun y => (-1 : ℝ) * realRicciDifferentialEnergy k (scalarCurvature k) y)
    hS (fun c => contDiffOn_const.mul (hQ c)) 3 x
  rw [scalarJetNorm_const_mul k hk _ hQ (-1) 3 x] at hMin
  have hdiff : (fun y => scalarHarnackSource k κ y +
      (-1 : ℝ) * realRicciDifferentialEnergy k (scalarCurvature k) y) = intrinsicHarnackMinimum k κ := by
    funext y
    simp only [intrinsicHarnackMinimum, sub_eq_add_neg, neg_one_mul]
  rw [hdiff] at hMin
  norm_num only [abs_neg, abs_one, one_mul] at hMin
  have H := hMin.trans (add_le_add hSource hEnergy)
  change scalarJetNorm k (intrinsicHarnackMinimum k κ) 3 x ≤ _
  unfold spatialHarnackJetBudget
  change scalarJetNorm k (intrinsicHarnackMinimum k κ) 3 x ≤
    1 + C05ScalarTimeSourceBoundsAux.b1 n B + K * B + 32 * (2*n : ℕ) * CA * B ^ 2
  linarith only [H]

end Yau.Proofs.C05SpatialHarnackBudgetAux
