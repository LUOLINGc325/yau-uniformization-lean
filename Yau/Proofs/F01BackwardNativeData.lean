import Yau.Proofs.F01NativeShiftedPoint
import Yau.Proofs.F01ShiftedNativeClock
import Yau.Proofs.F01ShiftedBackgroundJets
import Yau.Proofs.F01ClosedPotentialWordEquations

/-! The original native potential on a backward chart ending at its
actual terminal time. Smoothness, nonlinear clock jets and the full
word system use only times in the supplied closed flow interval. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shifted_backward_native_potential_smooth (A : BoundedChartFamily g)
    (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (shiftedNativePotential A U a ρ τ) (cylinder (ball 0 1) (-1) 0) := by
  have hMap : MapsTo (affineParabolicPoint ρ (0 : Space n) τ)
      (cylinder (ball 0 1) (-1) 0) (ball 0 A.radius ×ˢ Icc 0 T) :=
    fun p hp => ⟨shifted_space_maps A hρ hρr hp.1, shifted_backward_clock_maps hLower hUpper hp.2⟩
  have hAffine : ContDiff ℝ ∞ (affineParabolicPoint (n := n) ρ 0 τ) := by
    unfold affineParabolicPoint
    fun_prop
  exact contDiffOn_const.mul ((bounded_chart_spaceTime_smooth A hU a).comp hAffine.contDiffOn hMap)

theorem shifted_backward_native_clock_jet
    (A : BoundedChartFamily g) (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T ρ τ : ℝ} (hρ : ρ ≠ 0) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s) (a : M.Carrier)
    (x : Space n) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 0) :
    HasDerivWithinAt (fun s => shiftedNativePotential A U a ρ τ (x, s))
      (flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ (x, t)).1)
        (affineParabolicPoint ρ 0 τ (x, t)).2) (Icc (-1) 0) t :=
  affine_potential_clock_jet
    (u := fun q : Point n => U (A.chart a q.1) q.2)
    (P := fun q : Point n => flowLogDetRatio g h (A.chart a q.1) q.2)
    hρ ht (shifted_backward_clock_maps hLower hUpper)
    (fun s hs => hpde (A.chart a (ρ • x + 0)) s hs)

theorem shifted_backward_native_log_identity
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ cylinder (ball 0 1) (-1) 0) :
    flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ p).1)
      (affineParabolicPoint ρ 0 τ p).2 =
      Real.log (chartPotentialMatrix (shiftedComplexBackground A a ρ τ)
        (shiftedNativePotential A U a ρ τ) p).det.re + normalizedPotentialLogSource A a ρ p.1 := by
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  have ht := shifted_backward_clock_maps hLower hUpper hp.2
  rw [shifted_native_flow_matrix_at hg A h U hρ.ne' hU hpot a p hz ht]
  have hs := A.closedBall_source a (ball_subset_closedBall (shifted_space_maps A hρ hρr hp.1))
  have hh := flowLogDetRatio_pullback_difference g h (A.chart a)
    (A.differentiable a) (A.inverse_differentiable a) hs (affineParabolicPoint ρ 0 τ p).2
  simpa only [normalizedPotentialLogSource, BoundedChartFamily.backgroundLogDet,
    affineParabolicPoint, add_zero, sub_eq_add_neg] using hh

theorem shifted_backward_native_matrix_pos
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ cylinder (ball 0 1) (-1) 0) :
    (chartPotentialMatrix (shiftedComplexBackground A a ρ τ) (shiftedNativePotential A U a ρ τ) p).PosDef := by
  rw [shifted_native_flow_matrix_at hg A h U hρ.ne' hU hpot a p
    (spatialDilation_mem_ball hρ hρr hp.1) (shifted_backward_clock_maps hLower hUpper hp.2)]
  exact pullbackMatrix_posDef _ (A.chart a) (A.differentiable a) (A.inverse_differentiable a)
    (A.closedBall_source a (ball_subset_closedBall (shifted_space_maps A hρ hρr hp.1)))

theorem shifted_backward_native_word_equations
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s) (a : M.Carrier) (v : Space n) :
    PotentialWordEquationsOn (cylinder (ball 0 1) (-1) 0)
      (shiftedComplexBackground A a ρ τ) (shiftedNativePotential A U a ρ τ)
      (normalizedPotentialLogSource A a ρ) v := by
  refine smooth_potential_word_equations_on_closed_interval
    (shiftedComplexBackground A a ρ τ) (shiftedNativePotential A U a ρ τ)
    (normalizedPotentialLogSource A a ρ) isOpen_ball (by norm_num : (-1 : ℝ) < 0)
    (shifted_backward_native_potential_smooth A U hρ hρr hLower hUpper hU a)
    (fun t _ => shiftedComplexBackground_smooth_spatial_slice A hρ hρr τ a t)
    (normalizedPotentialLogSource_smooth A hρ hρr a)
    (fun p hp => shifted_backward_native_matrix_pos hg A h U hρ hρr hLower hUpper hU hpot a hp) ?_ v
  intro x hx t ht
  have hh := shifted_backward_native_clock_jet A h U hρ.ne' hLower hUpper hpde a x ht
  have hLog := shifted_backward_native_log_identity hg A h U hρ hρr hLower hUpper hU hpot a
    (p := (x, t)) ⟨hx, ht⟩
  exact hLog ▸ hh

end Yau.NodeProofs.F01Aux
