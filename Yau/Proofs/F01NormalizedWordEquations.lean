import Yau.Proofs.F01NormalizedInitialLogIdentity
import Yau.Proofs.F01NormalizedBackgroundRegularity
import Yau.Proofs.F01ZeroExtendedWordEquations

/-! The actual normalized native potential supplies every qualitative
word-equation input on the full initial cylinder. Its log identity,
clock jets, positivity and zero data are all derived from the original
flow and potential identities. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def PotentialSpatialWordEquations
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (V : Point n → ℝ)
    (b : Space n → ℝ) (v : Space n) : Prop :=
  let H := chartPotentialMatrix S V
  let w := spatialDerivativeWord [v] V
  let f := fun p => traceWith (H p)
    (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ b p.1 v
  ∀ vs : List (Space n), C2 (cylinder (ball 0 1) (-1) 1) (spatialDerivativeWord vs w) ∧
    ∀ p ∈ cylinder (ball 0 1) (-1) 1,
      linearOp (cylinder (ball 0 1) (-1) 1) (fun q => scalarSymbol (H q)) (fun _ _ => 0)
        (spatialDerivativeWord vs w) p =
        linearCommutatorSource (fun q => scalarSymbol (H q)) w f vs p

theorem normalized_rescale_initial_jet_data
    (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = g) (hU0 : ∀ x, U x 0 = 0)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s) (a : M.Carrier) :
    let u := parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2)
    let P := fun q : Point n => flowLogDetRatio g h (A.chart a (ρ • q.1)) (ρ ^ 2 * q.2)
    ContDiffOn ℝ ∞ u (ball 0 1 ×ˢ Icc 0 1) ∧
      (∀ x ∈ ball 0 1, u (x, 0) = 0) ∧
      (∀ x ∈ ball 0 1, P (x, 0) = 0) ∧
      ∀ x ∈ ball 0 1, ∀ t ∈ Icc 0 1,
        HasDerivWithinAt (fun s => u (x, s)) (P (x, t)) (Icc 0 1) t := by
  dsimp only
  refine ⟨parabolicRescalePotential_smooth hρ hρr hρT
    (bounded_chart_spaceTime_smooth A hU a), ?_, ?_, ?_⟩
  · intro x hx
    simp only [parabolicRescalePotential, parabolicDilation, mul_zero, hU0]
  · intro x hx
    rw [mul_zero]
    exact flowLogDetRatio_initial g h hh0 _
  · intro x hx t ht
    exact parabolicRescalePotential_time_jet
      (F := fun q : Point n => U (A.chart a q.1) q.2)
      (D := fun q : Point n => flowLogDetRatio g h (A.chart a q.1) q.2)
      hρ hρr hρT (fun z hz s hs => hpde (A.chart a z) s hs) (p := (x, t)) ⟨hx, ht⟩

theorem normalized_chart_potential_pos
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = g)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    (chartPotentialMatrix (normalizedComplexBackground A a ρ)
      (forwardZeroSpaceTime (parabolicRescalePotential ρ
        (fun q : Point n => U (A.chart a q.1) q.2))) p).PosDef := by
  have he : chartPotentialMatrix (normalizedComplexBackground A a ρ)
      (forwardZeroSpaceTime (parabolicRescalePotential ρ
        (fun q : Point n => U (A.chart a q.1) q.2))) p =
      pullbackMatrix (h (ρ ^ 2 * max p.2 0)) (A.chart a) (ρ • p.1) :=
    normalized_complex_flow_matrix hg A h U hρ hρr hρT hU hh0 hpot a hp
  rw [he]
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  exact pullbackMatrix_posDef _ (A.chart a) (A.differentiable a) (A.inverse_differentiable a)
    (A.closedBall_source a (ball_subset_closedBall hz))

theorem normalized_native_potential_word_equations
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρT : ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = g) (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s) (a : M.Carrier) (v : Space n) :
    PotentialSpatialWordEquations (normalizedComplexBackground A a ρ)
      (forwardZeroSpaceTime (parabolicRescalePotential ρ
        (fun q : Point n => U (A.chart a q.1) q.2)))
      (normalizedPotentialLogSource A a ρ) v := by
  let u := parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2)
  let P := fun q : Point n => flowLogDetRatio g h (A.chart a (ρ • q.1)) (ρ ^ 2 * q.2)
  let S := normalizedComplexBackground A a ρ
  let b := normalizedPotentialLogSource A a ρ
  have hData := normalized_rescale_initial_jet_data A h U hρ hρr hρT hU hh0 hU0 hpde a
  have hPos : ∀ p ∈ ball 0 1 ×ˢ Icc (-1) 1,
      (chartPotentialMatrix S (forwardZeroSpaceTime u) p).PosDef :=
    fun p hp => normalized_chart_potential_pos hg A h U hρ hρr hρT hU hh0 hpot a hp
  have hLog (p : Point n) (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
      forwardZeroSpaceTime P p = Real.log (chartPotentialMatrix S (forwardZeroSpaceTime u) p).det.re + b p.1 := by
    dsimp only [P, S, u, b, normalizedPotentialLogSource, BoundedChartFamily.backgroundLogDet]
    simpa only [sub_eq_add_neg] using
      normalized_initial_log_identity hg A h U hρ hρr hρT hU hh0 hpot a hp
  exact zero_extended_potential_word_equations S u P b isOpen_ball zero_lt_one (by norm_num)
    hData.1 hData.2.1 hData.2.2.1 hData.2.2.2
    (fun t _ => normalizedComplexBackground_smooth_spatial_slice A hρ hρr a t)
    (normalizedPotentialLogSource_smooth A hρ hρr a) hPos hLog v

end Yau.NodeProofs.F01Aux
