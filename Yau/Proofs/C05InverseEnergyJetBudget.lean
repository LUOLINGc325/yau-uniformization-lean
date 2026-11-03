import Yau.Proofs.C05InverseEnergyJetBudgetProduct
import Yau.Proofs.C05ActualInverseEnergyLaplacian

/-! Finite jets of the actual inverse Ricci differential energy, at one point. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05InverseEnergyJetBudgetAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05RicciSquareJetsAux
open Yau.Proofs.C05HessianPropagationAux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem computedJet_inverseFieldJet (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ) (m : ℕ) :
    Generic.jet k c (inverseFieldJet k c A 0) m = inverseFieldJet k c A m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change covariantD k c (Generic.jet k c (inverseFieldJet k c A 0) m) =
        covariantD k c (inverseFieldJet k c A m)
      rw [ih]

theorem scalarJetNorm_realRicciDifferentialEnergy_le (k : HermitianField M)
    (hk : MetricSmooth k) (hK : KahlerClosed k) (hA : ∀ y, (ricci k y).PosDef)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (m : ℕ) (hm : m ≤ 3) (x : M.Carrier)
    {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hC : ∀ j ≤ 3, metricTensorNorm (realMetricFn k x (chartPt x x))
      (inverseFieldJet k x (fun z => Matrix.of (realRicciCoeff k x z)) j (chartPt x x)) ≤ CA)
    (hF : ∀ j ≤ 4, scalarJetNorm k f j x ≤ CB) :
    scalarJetNorm k (realRicciDifferentialEnergy k f) m x ≤ 32*(2*n:ℕ)*CA*CB^2 := by
  let C := ricciInverseTensor k x
  let p := scalarJet k f x 1
  let P := fun w => tensorConcatProduct (p w) (p w)
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hJC (j : ℕ) (hj : j ≤ 3) : metricTensorNorm (realMetricFn k x (chartPt x x))
      (Generic.jet k x C j (chartPt x x)) ≤ CA := by
    change metricTensorNorm _ (Generic.jet k x
      (inverseFieldJet k x (fun z => Matrix.of (realRicciCoeff k x z)) 0) j _) ≤ CA
    rw [computedJet_inverseFieldJet]
    exact hC j hj
  have hJP := differential_square_jets_le k hk f hf x hCB hF
  have hP (v : Fin 2 → RIdx n) : ContDiffOn ℝ ∞ (fun w => P w v) (chartTarget x) :=
    (scalarJet_contDiffOn k hk f hf x 1 _).mul (scalarJet_contDiffOn k hk f hf x 1 _)
  have H := Generic.word_covariantJet_norm_le_three ricciSquareWord k hk x C P
    (ricciInverseTensor_contDiffOn k hk hK hA x) hP hz hCA
    (by positivity : (0:ℝ) ≤ 8*CB^2) hJC hJP m hm
  have he : ∀ z ∈ chartTarget x, ∀ v : Fin 0 → RIdx n,
      ricciSquareWord.eval (realMetricFn k x z)⁻¹ (C z) (P z) v =
        inChart x (fun y => 2*realRicciDifferentialEnergy k f y) z := by
    intro z hz v
    rw [ricciPairWord_eval]
    change _ = 2*realRicciDifferentialEnergy k f (chartInv x z)
    rw [← ricciInverseEnergyInChart_eq_global k hk f hf x hz,
      ricciInverseEnergyInChart_eq_pair k f x hz]
    dsimp only [C,P,p,covectorSquare]
    ring
  rw [computedScalarJet_norm_eq k x (fun y => 2*realRicciDifferentialEnergy k f y) _
    (isOpen_extChartAt_target (I := ComplexModel n) x) he hz m hm] at H
  change scalarJetNorm k (fun y => 2*realRicciDifferentialEnergy k f y) m x ≤ _ at H
  rw [scalarJetNorm_const_mul k hk _
    (realRicciDifferentialEnergy_smoothFn k hk hK hA f hf) 2 m x] at H
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at H
  nlinarith

end Yau.Proofs.C05InverseEnergyJetBudgetAux
