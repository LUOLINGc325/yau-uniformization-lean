import Yau.Proofs.C03EnvelopeSmoothingStrict
import Yau.Proofs.C03EnvelopeSmoothingRadius

/-! One actual convolution of the continuous envelope, with the frozen quantitative bounds. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder Convolution
open Filter Set Metric MeasureTheory
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.Blueprint Yau.LeafProofs L22Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem exists_smooth_envelope_on_ball
    (rEnv R : ℝ) (hR : 0 < R) (hRenv : R < rEnv)
    (f : ComplexVector n → ℝ) (hfc : ContinuousOn f (ball 0 rEnv))
    (hsupport : PlanarLowerSupports f (ball 0 rEnv) (fun _ _ => 0))
    (S T : Set (ComplexVector n)) (hS : IsOpen S) (_hSO : S ⊆ ball 0 rEnv)
    (hT : IsCompact T) (hTS : T ⊆ S) (hTD : T ⊆ ball 0 R)
    (H : ComplexVector n → Herm n) (hHc : ∀ i j, Continuous (fun z => H z i j))
    (hHp : ∀ z, (H z).PosDef) (kappa : ℝ) (hkappa : 0 < kappa)
    (hstrict : PlanarLowerSupports f S (fun z v => 4 * kappa * matrixQuadratic (H z) v))
    (hnonneg : ∀ z ∈ S, 0 ≤ f z) (M : ℝ) (hupper : ∀ z ∈ ball 0 rEnv, f z ≤ M) :
    IsPshOn (fun z => (f z : EReal)) (ball 0 rEnv) ∧
      ∃ g : ComplexVector n → ℝ, ContDiff ℝ ∞ g ∧
        (∀ z ∈ ball 0 R, (leviC g z).PosSemidef ∧ g z ≤ M) ∧
        ∀ z ∈ T, 0 ≤ g z ∧ HermLE (((kappa / 2 : ℝ) : ℂ) • H z) (leviC g z) := by
  have hpsh := complexLinePshOn_of_planar_lower_supports (ball 0 rEnv) f hfc hsupport
  refine ⟨isPshOn_of_complexLinePshOn hpsh, ?_⟩
  obtain ⟨s, d, hs, hRs, hsEnv, hd, htrans, hlocal⟩ :=
    exists_common_smoothing_radius R rEnv hR hRenv S T hS hT hTS hTD H hHc hHp
  have hclosed : closedBall (0 : ComplexVector n) s ⊆ ball 0 rEnv := by
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hsEnv)
  obtain ⟨F, hFc, _hFs, _hFi, hEq⟩ :=
    exists_continuous_compact_extension s hs f (hfc.mono hclosed)
  let phi : ContDiffBump (0 : ComplexVector n) := ⟨d / 2, d, half_pos hd, half_lt_self hd⟩
  let g : ComplexVector n → ℝ := normalizedConvolution phi F
  have hgs : ContDiff ℝ ∞ g := normalizedConvolution_smooth phi F hFc
  have hEqBall : EqOn F f (ball (0 : ComplexVector n) s) :=
    fun _ hz => hEq (ball_subset_closedBall hz)
  have hpshBall : LeafCandidates.ComplexLinePshOn (ball (0 : ComplexVector n) s) f :=
    complexLinePshOn_mono hpsh (ball_subset_closedBall.trans hclosed)
  have hgpsh : LeafCandidates.ComplexLinePshOn (ball (0 : ComplexVector n) R) g :=
    normalized_convolution_psh hpshBall hFc hEqBall phi htrans
  refine ⟨g, hgs, ?_, ?_⟩
  · intro z hz
    refine ⟨leviC_posSemidef_of_smooth_psh isOpen_ball hgpsh hgs hz, ?_⟩
    apply normalizedConvolution_le phi F hFc z M
    intro a ha
    have hpoint := htrans z hz a ha
    rw [hEqBall hpoint]
    exact hupper _ (hclosed (ball_subset_closedBall hpoint))
  · intro z hz
    obtain ⟨hzS, hzO, hzH⟩ := hlocal z hz
    refine ⟨?_, ?_⟩
    · apply normalizedConvolution_nonneg phi F z
      intro a ha
      have hpoint := htrans z (hTD hz) a ha
      rw [hEqBall hpoint]
      apply hnonneg
      apply hzS
      rw [mem_ball]
      have ha' : ‖a‖ ≤ d := by simpa only [mem_closedBall, dist_zero_right] using ha
      have heq : dist (z - a) z = ‖a‖ := by simp [dist_eq_norm]
      rw [heq]
      linarith
    · exact normalizedConvolution_strict_at (ball 0 s) S f F
        (hfc.mono (ball_subset_closedBall.trans hclosed)) hFc hEqBall H kappa hkappa
        hstrict phi z d hd le_rfl hzO hzS (hHp z).isHermitian hzH

end Yau.Proofs.C03Aux.EnvelopeSmoothing
