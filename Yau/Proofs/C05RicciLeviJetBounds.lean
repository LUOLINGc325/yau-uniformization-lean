import Yau.Proofs.C05RicciHessianPair
import Yau.Proofs.C05ScalarJetChartField
import Yau.Proofs.C05ScalarJetLinearity

/-! Intrinsic derivative bounds for the actual Ricci--Levi contraction. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux Yau.Proofs.C05RicciSquareJetsAux
open Yau.Proofs.C05RicciPropagationAux Yau.Proofs.C05HessianPropagationAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem computedJet_scalarJet (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (r m : ℕ) :
    Generic.jet k c (scalarJet k f c r) m = scalarJet k f c (r+m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change covariantD k c (Generic.jet k c (scalarJet k f c r) m) =
        covariantD k c (scalarJet k f c (r+m))
      rw [ih]

theorem computedJet_realRicciJet (k : HermitianField M) (c : M.Carrier) (m : ℕ) :
    Generic.jet k c (realRicciJet k c 0) m = realRicciJet k c m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change covariantD k c (Generic.jet k c (realRicciJet k c 0) m) =
        covariantD k c (realRicciJet k c m)
      rw [ih]

theorem scalarJetNorm_ricciLeviPairing_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (m : ℕ) (hm : m ≤ 2) (x : M.Carrier) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hA : ∀ j ≤ 3, realRicciJetNorm k j x ≤ CA)
    (hB : ∀ j ≤ 5, scalarJetNorm k f j x ≤ CB) :
    scalarJetNorm k (ricciLeviPairing k f) m x ≤ 4*(2*n:ℕ)*CA*CB := by
  let A := realRicciJet k x 0
  let B := scalarJet k f x 2
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hJA (j : ℕ) (hj : j ≤ 3) : metricTensorNorm (realMetricFn k x (chartPt x x))
      (Generic.jet k x A j (chartPt x x)) ≤ CA := by
    dsimp [A]
    rw [computedJet_realRicciJet]
    exact hA j hj
  have hJB (j : ℕ) (hj : j ≤ 3) : metricTensorNorm (realMetricFn k x (chartPt x x))
      (Generic.jet k x B j (chartPt x x)) ≤ CB := by
    dsimp [B]
    rw [computedJet_scalarJet]
    exact hB (2+j) (by omega)
  have H := Generic.word_covariantJet_norm_le_three ricciSquareWord k hk x A B
    (realRicciJet_contDiffOn k hk x 0) (scalarJet_contDiffOn k hk f hf x 2)
    hz hCA hCB hJA hJB m (by omega)
  have he : ∀ z ∈ chartTarget x, ∀ v : Fin 0 → RIdx n,
      ricciSquareWord.eval (realMetricFn k x z)⁻¹ (A z) (B z) v =
        inChart x (fun y => 2*ricciLeviPairing k f y) z := by
    intro z hz v
    rw [ricciPairWord_eval]
    change _ = 2*inChart x (ricciLeviPairing k f) z
    rw [ricciLeviPairing_inChart k hk hK f hf x hz]
    dsimp [A,B]
    ring
  rw [computedScalarJet_norm_eq k x (fun y => 2*ricciLeviPairing k f y) _
    (isOpen_extChartAt_target (I := ComplexModel n) x) he hz m (by omega)] at H
  change scalarJetNorm k (fun y => 2*ricciLeviPairing k f y) m x ≤ _ at H
  rw [scalarJetNorm_const_mul k hk _ (ricciLeviPairing_smoothFn k hk hK f hf) 2 m x] at H
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at H
  linarith

end Yau.Proofs.C05Aux
