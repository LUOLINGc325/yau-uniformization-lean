import Yau.Proofs.F03EllipticUniformPowerBound
import Yau.Proofs.F03EllipticCoefficientBounds

/-! Every true compact heat error has a local O(t) bound for each actual spatial tensor order. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

theorem wholeCompactHeat_local_jet_rate
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (a : M.Carrier) (c : ComplexVector n)
    (hc : c ∈ chartTarget a) (m : ℕ) :
    ∃ r : ℝ,0 < r ∧ ∃ C : ℝ,0 < C ∧ ∀ t,0 < t → ∀ w ∈ Metric.ball (0 : ComplexVector n) r,
      ‖iteratedFDeriv ℝ m (fun z =>
        wholeCompactHeat g hK μ hμ k (chartInv a z) t-k (chartInv a z)) (w+c)‖ ≤ C*t := by
  obtain ⟨delta,hDelta,hDeltaSub⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := ComplexModel n) a) c hc
  let R := delta/2
  let r := delta/4
  have hR : 0 < R := half_pos hDelta
  have hr : 0 < r := by dsimp [r];positivity
  have hrR : r < R := by dsimp [r,R];linarith
  have hRDelta : R < delta := half_lt_self hDelta
  let D : Set (ComplexVector n) := {w | w+c ∈ chartTarget a}
  have hD : IsOpen D := (isOpen_extChartAt_target (I := ComplexModel n) a).preimage
    (continuous_id.add continuous_const)
  have hBall : Metric.closedBall (0 : ComplexVector n) R ⊆ D := by
    intro w hw
    apply hDeltaSub
    have hNorm : ‖w‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right] using hNorm.trans_lt hRDelta
  let A : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ := fun w => scalarHeatChartCoeff g a (w+c,0)
  have ha : ∀ i j,ContDiffOn ℝ ∞ (fun w => A w i j) D := by
    intro i j
    have hBase : ContDiffOn ℝ ∞ (fun z => scalarHeatChartCoeff g a (z,0) i j) (chartTarget a) := by
      simpa only [scalarHeatChartCoeff] using
        ((contDiffOn_const (c := (1/2 : ℝ))).mul (realMetricFn_inverse_contDiffOn g a i j))
    exact hBase.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hw => hw)
  have hb : ∀ i : RIdx n,ContDiffOn ℝ ∞ (fun _ : ComplexVector n => (0 : ℝ)) D :=
    fun _ => contDiffOn_const
  let N := m+n+1
  have hOrder : m+n < 2*N := by dsimp [N];omega
  obtain ⟨AC,hAC,hCoeff⟩ := elliptic_coefficients_compact_jet_bounds D hD A (fun _ _ => 0)
    ha hb (Metric.closedBall 0 R) (isCompact_closedBall 0 R) hBall (2*N+1)
  let Q : Set (ComplexVector n) := (fun w : ComplexVector n => w+c) '' Metric.closedBall 0 R
  have hQ : IsCompact Q := (isCompact_closedBall (0 : ComplexVector n) R).image
    (continuous_id.add continuous_const)
  have hQt : Q ⊆ chartTarget a := by
    rintro z ⟨w,hw,rfl⟩
    exact hBall hw
  obtain ⟨lam,upper,hEll⟩ := scalarHeatChartCoeff_elliptic g a hQ hQt ({0} : Set ℝ)
  have hLower : ∀ z ∈ Metric.ball (0 : ComplexVector n) R,∀ v : RIdx n → ℝ,
      lam*∑ i,(v i)^2 ≤ ∑ i,∑ j,A z i j*v i*v j := by
    intro z hz v
    exact ((hEll.2.2 (z+c,0) ⟨⟨z,Metric.ball_subset_closedBall hz,rfl⟩,mem_singleton _⟩).2 v).1
  have hSub : Metric.ball (0 : ComplexVector n) R ⊆ D := Metric.ball_subset_closedBall.trans hBall
  obtain ⟨CT,hCT,hTensor⟩ := elliptic_tensor_bound_of_uniform_powers n (complexManifold_dimension_pos M)
    m N hOrder r R lam AC hr hrR hEll.1 hAC
  have hPowers : ∀ p : Fin (N+1),∃ K : ℝ,0 < K ∧ ∀ t,0 < t →
      ContDiffOn ℝ ∞
        ((ellipticOp A (fun _ _ => 0))^[p.val]
          (fun w => ((wholeCompactHeat g hK μ hμ k (chartInv a (w+c)) t-k (chartInv a (w+c)) : ℝ) : ℂ))) D ∧
      ∀ w,w+c ∈ chartTarget a →
        ‖((ellipticOp A (fun _ _ => 0))^[p.val]
          (fun z => ((wholeCompactHeat g hK μ hμ k (chartInv a (z+c)) t-k (chartInv a (z+c)) : ℝ) : ℂ))) w‖ ≤ K*t :=
    fun p => wholeCompactHeat_shifted_chart_power_rate g hK μ hμ k a c p.val
  choose Kp hKp hPower using hPowers
  let B := 1+∑ p,Kp p
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun p _ => (hKp p).le))
  have hpB (p : Fin (N+1)) : Kp p ≤ B :=
    (Finset.single_le_sum (fun q _ => (hKp q).le) (Finset.mem_univ p)).trans (by dsimp [B];linarith)
  refine ⟨r,hr,CT*B,mul_pos hCT hB,fun t ht w hw => ?_⟩
  let u : ComplexVector n → ℝ := fun z => wholeCompactHeat g hK μ hμ k (chartInv a z) t-k (chartInv a z)
  have hAll : ∀ p ≤ N,ContDiffOn ℝ ∞
      ((ellipticOp A (fun _ _ => 0))^[p] (fun z => (u (z+c) : ℂ))) D :=
    fun p hp => (hPower ⟨p,by omega⟩ t ht).1
  have hUniform : ∀ p ≤ N,∀ z ∈ Metric.ball (0 : ComplexVector n) R,
      ‖((ellipticOp A (fun _ _ => 0))^[p] (fun q => (u (q+c) : ℂ))) z‖ ≤ B*t := by
    intro p hp z hz
    exact ((hPower ⟨p,by omega⟩ t ht).2 z (hSub hz)).trans
      (mul_le_mul_of_nonneg_right (hpB ⟨p,by omega⟩) ht.le)
  have hTensorBound := hTensor A (fun _ _ => 0) (fun i j => (ha i j).mono hSub)
    (fun i => (hb i).mono hSub) hLower
    (fun j hj z hz i l => hCoeff j hj z (Metric.ball_subset_closedBall hz) i l)
    D hD hBall (fun z => (u (z+c) : ℂ)) hAll (B*t) (mul_nonneg hB.le ht.le) hUniform w hw
  have hError := smoothFn_sub (smoothFn_of_smoothSpaceTime (wholeCompactHeat_smooth g hK μ hμ k) ht) k.2.1
  have hReal : ContDiffOn ℝ ∞ (fun z => u (z+c)) D :=
    (hError a).comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hz => hz)
  have hwD : w ∈ D := hSub (Metric.ball_subset_ball hrR.le hw)
  have hNorm := norm_iteratedFDeriv_ofReal (hReal.contDiffAt (hD.mem_nhds hwD)) m
  have hShift := congrArg norm (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := u) m c w)
  have hRealNorm := hNorm.trans hShift
  exact hRealNorm.symm.trans_le (hTensorBound.trans_eq (by ring))

end Yau.Proofs.F03Aux
