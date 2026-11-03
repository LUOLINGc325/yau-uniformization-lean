import Yau.Proofs.C02NativeWordEnergy
import Yau.Proofs.C02UniformAffineGraphScale
import Yau.Proofs.C02CoordinateCorrections
import Yau.Proofs.C02RescaledCorrectionBounds
import Yau.Proofs.C02RescaledCorrectionJets
import Yau.LeafProofs.L21ColumnCoordinates

/-! The same F is tested at every finite order; rescaling changes only the proof.
All constants precede the graph field, correcting map and evaluation centre. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L21Aux
variable {n : ℕ}

theorem model_ball_isCompact_closure (R : ℝ) :
    IsCompact (closure (Metric.ball (0 : ComplexVector n) R)) :=
  (isCompact_closedBall (0 : ComplexVector n) R).of_isClosed_subset isClosed_closure
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)

theorem coordinateCorrection_dbarA
    (A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (F : ComplexVector n → ComplexVector n) (hF : ContDiff ℝ ∞ F)
    (x : ComplexVector n) (k : Fin n)
    (hEquation : ∀ i, dbarA A i (fun y => F y k) x = 0) (i : Fin n) :
    dbarA A i (coordinateCorrection F k) x = A x i k := by
  let pr := (EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ
  have hProj : DifferentiableAt ℝ (fun y : ComplexVector n => y k) x :=
    (pr.hasFDerivAt (x := x)).differentiableAt
  have hComponent : DifferentiableAt ℝ (fun y => F y k) x :=
    (pr.hasFDerivAt.comp x
      (hF.differentiable (by simp) x).hasFDerivAt).differentiableAt
  change dbarA A i ((fun y : ComplexVector n => y k) - fun y => F y k) x = _
  rw [dbarA_sub A i hProj hComponent, dbarA_coordinate, hEquation, sub_zero]

theorem exists_uniform_coordinate_jet_bound (n : ℕ) (K : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 < B ∧
      ∀ A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ,
      MatrixSmoothOn A (Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
        Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k, ‖A x i k‖ ≤ 1) →
      (∀ j, 1 ≤ j → ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k,
        ‖iteratedFDeriv ℝ j (fun y => A y i k) x‖ ≤ K j) →
      ∀ F : ComplexVector n → ComplexVector n, ContDiff ℝ ∞ F →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k,
        dbarA A i (fun y => F y k) x = 0) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
        ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4) →
      ∀ a ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ), ‖iteratedFDeriv ℝ m F a‖ ≤ B := by
  let O := Metric.ball (0 : ComplexVector n) 1
  let R := Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ)
  have hOR : closure R ⊆ O :=
    (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨s, hs, hs8, hScale⟩ := exists_uniform_affine_graph_scale n (realDimension n + m) K
  obtain ⟨C, hC, hWord⟩ := exists_inner_word_column_bound (n := n) m
    Metric.isOpen_ball (model_ball_isCompact_closure _) Metric.isOpen_ball
    (model_ball_isCompact_closure _) hOR
  let V : ℝ := ∫ x in O, (1 : ℝ) ∂lebesgueC n
  have hV : 0 ≤ V := integral_nonneg fun _ => zero_le_one
  let D := C * (V + 1) + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  let B0 := (s⁻¹) ^ (m - 1) * ((realDimension n : ℝ) ^ m * D)
  have hB0 : 0 ≤ B0 := by dsimp only [B0]; positivity
  refine ⟨(n : ℝ) * (1 + B0) + 1, by positivity, ?_⟩
  intro A hA hsmall hValue hJets F hF hEquation hClose a ha
  obtain ⟨hMaps, hASmooth, hAJet⟩ := hScale A hA hValue hJets a ha
  have hASmall (z : ComplexVector n) (hz : z ∈ O) :
      Yau.LeafCandidates.matrixOpNorm (A (a + s • z)) ≤ 1 / 2 := hsmall _ (hMaps hz)
  have hCorr (k : Fin n) : ‖iteratedFDeriv ℝ m (coordinateCorrection F k) a‖ ≤ B0 := by
    let w := coordinateCorrection F k
    let v := rescaledCorrection s a w
    have hw : ContDiff ℝ ∞ w := coordinateCorrection_contDiff F hF k
    have hv : ContDiff ℝ ∞ v := rescaledCorrection_contDiff s a w hw
    have hVBound (z : ComplexVector n) (hz : z ∈ O) : ‖v z‖ ≤ (1 / 4 : ℝ) := by
      have h := rescaledCorrection_norm_le s hs.ne' a w hw hMaps (1 / 4 : ℝ)
        (fun y hy => (coordinateCorrection_fderiv_norm_le
          (hF.differentiable (by simp) y) k).trans (hClose y hy)) hz
      have hzN : ‖z‖ < (1 : ℝ) := by simpa only [O, Metric.mem_ball, dist_zero_right] using hz
      exact h.trans (by linarith)
    have hMass := (bounded_local_scalar_energy Metric.isOpen_ball (model_ball_isCompact_closure _)
      v hv.continuous.continuousOn (by norm_num : (0 : ℝ) ≤ 1 / 4) hVBound).2
    have hMass' : (∫ z in O, ‖v z‖ ^ 2 ∂lebesgueC n) ≤ V := by
      apply hMass.trans
      change (1 / 4 : ℝ) ^ 2 * V ≤ V
      nlinarith
    have hEq (z : ComplexVector n) (hz : z ∈ O) (i : Fin n) :
        dbarA (fun y => A (a + s • y)) i v z = A (a + s • z) i k := by
      rw [rescaledCorrection_dbarA A s hs.ne' a w z (hw.differentiable (by simp) _) i]
      exact coordinateCorrection_dbarA A F hF _ k (fun j => hEquation _ (hMaps hz) j k) i
    have hWords (w' : List (RIdx n)) (hw' : w'.length = m) : ‖wordDerivative v w' 0‖ ≤ D := by
      have h := hWord (fun y => A (a + s • y)) hASmooth hASmall hAJet
        1 zero_le_one hAJet v hv k hEq w' hw'.le 0 (by simp)
      have hMassPlus : (∫ z in O, ‖v z‖ ^ 2 ∂lebesgueC n) + 1 ≤ V + 1 := by
        linarith only [hMass']
      have hSquare : ‖wordDerivative v w' 0‖ ^ 2 ≤ C * (V + 1) :=
        h.trans (mul_le_mul_of_nonneg_left (by simpa only [one_pow] using hMassPlus) hC.le)
      dsimp only [D]
      nlinarith [norm_nonneg (wordDerivative v w' 0)]
    have hJet := norm_jet_le_native_word_bound v hv m 0 D hD.le hWords
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    dsimp only [B0, w]
    simpa only [Nat.add_sub_cancel, Nat.succ_eq_add_one] using
      jet_norm_le_of_rescaledCorrection_bound s hs a w hw l _ hJet
  exact (coordinate_map_positive_jet_bound_of_corrections F hF m hm a B0 hCorr).trans (by linarith)

theorem exists_uniform_coordinate_jet_profile (n : ℕ) (K : ℕ → ℝ) :
    ∃ b : ℕ → ℝ, (∀ j, 0 < b j) ∧
      ∀ A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ,
      MatrixSmoothOn A (Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
        Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k, ‖A x i k‖ ≤ 1) →
      (∀ j, 1 ≤ j → ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k,
        ‖iteratedFDeriv ℝ j (fun y => A y i k) x‖ ≤ K j) →
      ∀ F : ComplexVector n → ComplexVector n, ContDiff ℝ ∞ F →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ i k,
        dbarA A i (fun y => F y k) x = 0) →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
        ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ 1 / 4) →
      ∀ j, 1 ≤ j → ∀ a ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ),
        ‖iteratedFDeriv ℝ j F a‖ ≤ b j := by
  choose B hB hRegular using fun j : ℕ => exists_uniform_coordinate_jet_bound n K (j + 1) (by omega)
  refine ⟨fun j => B (j - 1), fun j => hB (j - 1), ?_⟩
  intro A hA hsmall hValue hJets F hF hEquation hClose j hj a ha
  have h := hRegular (j - 1) A hA hsmall hValue hJets F hF hEquation hClose a ha
  have hjEq : j - 1 + 1 = j := by omega
  rw [hjEq] at h
  exact h

end Yau.Blueprint.C02Proof
