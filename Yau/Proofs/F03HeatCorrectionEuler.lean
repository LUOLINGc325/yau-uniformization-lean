import Yau.Proofs.F03HeatCorrectionTimeDerivative

/-! The actual correction's time-Euler expression is the heat of the actual nonnegative potential defect. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem localizedFlow_potential_euler_bounds
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {s : ℝ} (hs : 0 ≤ s) (x : Pt X) :
    0 ≤ U x s-s*P x s ∧ U x s-s*P x s ≤ s*ρ x s := by
  have hρ := (hf.2.2.2.2.2.2.2.2.2.1 x s hs).1
  have hLow := F02Aux.neg_potential_le_time_mul_rho X o h U P ρ hf hs x
  have hU := F02Aux.potential_nonpos X o h U P ρ hf hs x
  rw [hρ] at hLow ⊢
  constructor <;> nlinarith

theorem metricDefectHeatCorrection_timeEulerWithin_identity
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s ∈ Icc 0 T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {L : ℝ} (hL : 0 < L) (x : Pt X) :
    metricDefectHeatCorrection X h μ hμ O hO L x s-
      s*metricDefectHeatCorrectionTimeDerivative X h U P μ hμ O hO T L x s=
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*
        (U y s-s*P y s) ∂μ)-(U x s-s*P x s) := by
  let H := dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO
  have hInt := dirichletMinimalKernel_potential_slab_integrable X o h U P ρ hf hT.le μ hμ O hO
    (sq_pos_of_pos hL) x hs
  have hHeat : (∫ y,H (L^2) x y*(U y s-s*P y s) ∂μ)=
      (∫ y,H (L^2) x y*U y s ∂μ)-s*(∫ y,H (L^2) x y*P y s ∂μ) := by
    calc
      _ = ∫ y,H (L^2) x y*U y s-s*(H (L^2) x y*P y s) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun y => by
          change H (L^2) x y*(U y s-s*P y s)=H (L^2) x y*U y s-s*(H (L^2) x y*P y s)
          ring)
      _ = _ := by rw [integral_sub hInt.2 (hInt.1.const_mul s),integral_const_mul]
  have hId := metricDefectHeatCorrection_centered_identity X o h U P ρ hf u hu hT hs μ hμ O hO hL x
  rw [dirichletMinimalKernel_centered_eq X o h U P ρ hf hT.le μ hμ O hO (sq_pos_of_pos hL) x hs] at hId
  change metricDefectHeatCorrection X h μ hμ O hO L x s-
    s*metricDefectHeatCorrectionTimeDerivative X h U P μ hμ O hO T L x s=
      (∫ y,H (L^2) x y*(U y s-s*P y s) ∂μ)-(U x s-s*P x s)
  rw [hHeat,hId]
  unfold metricDefectHeatCorrectionTimeDerivative centeredFlowPotential
  change _ = (∫ y,H (L^2) x y*U y s ∂μ)-s*(∫ y,H (L^2) x y*P y s ∂μ)-(U x s-s*P x s)
  dsimp only [H]
  ring

theorem metricDefectHeatCorrection_timeEuler_identity
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {L : ℝ} (hL : 0 < L)
    (x : Pt X) {s : ℝ} (hs : 0 < s) :
    metricDefectHeatCorrection X h μ hμ O hO L x s-
      s*deriv (metricDefectHeatCorrection X h μ hμ O hO L x) s=
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*
        (U y s-s*P y s) ∂μ)-(U x s-s*P x s) := by
  have hT : 0 < s+1 := by linarith
  have hMem : s ∈ Icc (0:ℝ) (s+1) := ⟨hs.le,by linarith⟩
  have hD := (metricDefectHeatCorrection_hasDerivWithinAt X o h U P ρ hf u hu hT μ hμ O hO hL x hMem).hasDerivAt
    (Icc_mem_nhds hs (by linarith))
  rw [hD.deriv]
  exact metricDefectHeatCorrection_timeEulerWithin_identity X o h U P ρ hf u hu hT hMem μ hμ O hO hL x

end Yau.Proofs.F03Aux
