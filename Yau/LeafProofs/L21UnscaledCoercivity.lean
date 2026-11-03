import Yau.LeafProofs.L21CorrectedBasicEstimate
import Yau.LeafProofs.L21LeviRemainderBounds
import Yau.LeafProofs.L21WeightedLeviPositive

/-! The actual compact weighted estimate for D and its weighted adjoint,
with dimension-dependent constants fixed before the graph coefficients. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem exists_uniform_unscaled_coercivity (n : ℕ) :
    ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
    ∀ (A : X n → Matrix (Fin n) (Fin n) ℂ),
      ∀ hA : MatrixSmoothOn A (Metric.ball (0 : X n) 1),
      JetBound 1 ε A (Metric.ball 0 1) → JetBound 2 1 A (Metric.ball 0 1) →
      ∀ K : ℝ, 4 * C0 ≤ K → ∀ v : Fin n → CompactTest (Metric.ball (0 : X n) 1),
        (K / 4) * coreScalarEnergy (boundaryWeight K) (fun i => testRhoInverse (v i)) ≤
          compactFormQ Metric.isOpen_ball hA
            (contDiffOn_boundaryWeight K) v := by
  obtain ⟨ε, C, hε, hC, hFrame⟩ := exists_uniform_corrected_levi n
  let M : ℝ := C * (n : ℝ) ^ 2
  let Z : ℝ := 4 * (n : ℝ) * C
  let R : ℝ := (n : ℝ) * M * (realDimension n : ℝ) + 4 * (n : ℝ) * (realDimension n : ℝ)
  let C0 : ℝ := coercivityRemainderConstant n M Z R + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC0 : 0 < C0 := by
    have hh := coercivityRemainderConstant_nonneg n M Z R
    dsimp [C0]
    linarith
  refine ⟨ε, C0, hε, hC0, ?_⟩
  intro A hA hSmall hJet K hK v
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨c, d, hSmooth, hValues, hDerivatives, hConj, hBracket, hLevi⟩ :=
    hFrame (Metric.ball 0 1) A Metric.isOpen_ball hA hSmall hJet
  have hc := fun i j k => (hSmooth i j k).1
  have hd := fun i j k => (hSmooth i j k).2
  have hValue (x : X n) (hx : x ∈ Metric.ball (0 : X n) 1) (i j k : Fin n) :
      ‖c i j k x‖ ≤ M ∧ ‖d i j k x‖ ≤ M := by
    have hDA := mul_le_mul_of_nonneg_left (mixedFrameDerivativeSize_le hJet hx) hC.le
    exact ⟨(hValues x hx i j k).1.trans hDA, (hValues x hx i j k).2.trans hDA⟩
  have hDd (x : X n) (hx : x ∈ Metric.ball (0 : X n) 1) (i j k : Fin n) :
      ‖dbarA A k (fun y => star (d i j k y)) x‖ ≤ Z := by
    have hp (a : Yau.RIdx n) := mixedFrame_row_norm
      (fun r s => (mixedFrame_jet_fderiv hJet hx r s).1) k a
    have hh := mixedFrame_rowApply_norm (dbarRealCoefficient A k) (fun y => star (d i j k y)) x hp
    change ‖∑ a : Yau.RIdx n, dbarRealCoefficient A k a x *
      fderiv ℝ (fun y => star (d i j k y)) x (Yau.realVec a)‖ ≤ _ at hh
    rw [← dbarA_eq_real_rows, mixedFrame_fderiv_star_norm] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hDerivatives x hx i j k).2
      (by positivity)).trans_eq (by dsimp [Z]; ring))
  have hRem (x : X n) (hx : x ∈ Metric.ball (0 : X n) 1) (i j : Fin n) :
      ‖weightedCommutatorRemainder A d i j x‖ ≤ R :=
    weightedCommutatorRemainder_norm_bound Metric.isOpen_ball hA hJet d hM
      (fun y hy r s k => (hValue y hy r s k).2) hx i j
  have hBasic := corrected_basic_lower_bound Metric.isOpen_ball hA (contDiffOn_boundaryWeight K)
    c d hc hd hBracket hM hZ hR (fun x hx i j k => (hValue x hx i j k).1)
      (fun x hx i j k => (hValue x hx i j k).2) hDd hRem v
  have hPositive := coreLeviEnergy_boundaryWeight_lower hA hd hK0
    (fun x hx ξ => hLevi K hK0 x hx hx ξ) v
  have hInverse := coreScalarEnergy_le_inverse K v
  have hBound := mul_le_mul_of_nonneg_left hInverse (coercivityRemainderConstant_nonneg n M Z R)
  have hGradient := coreGradientEnergy_nonneg Metric.isOpen_ball hA (boundaryWeight K) v
  have hInvNonneg := coreScalarEnergy_nonneg (boundaryWeight K) (fun i => testRhoInverse (v i))
  have hC0K : 4 * coercivityRemainderConstant n M Z R ≤ K := by dsimp [C0] at hK; linarith
  have hKmass := mul_le_mul_of_nonneg_right hC0K hInvNonneg
  linarith

end Yau.LeafProofs.L21Aux
