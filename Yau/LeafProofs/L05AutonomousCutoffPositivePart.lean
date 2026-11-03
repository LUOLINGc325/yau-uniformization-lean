import Yau.LeafProofs.L05AutonomousMollifierAverage

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A true lower bound and a fixed cutoff pairing control the positive part on the inner ball. -/
theorem auto_cutoff_positive_integral {n : ℕ} {r R B E : ℝ} (hrR : r≤ R) (hB : 0≤ B)
    {q φ : Space n → ℝ} (hq : ContinuousOn q (Metric.closedBall 0 R))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hφ0 : ∀ x, 0≤ φ x)
    (hsupp : tsupport φ⊆Metric.closedBall (0 : Space n) R)
    (hone : ∀ x∈Metric.closedBall (0 : Space n) r, φ x=1)
    (hlower : ∀ x∈Metric.closedBall (0 : Space n) R, -B≤ q x)
    (hpair : Integrable (fun x => φ x*q x)) (hPairBound : |∫ x, φ x*q x|≤ E) :
    IntegrableOn (fun x => max (q x) 0) (Metric.ball (0 : Space n) r) ∧
      (∫ x in Metric.ball (0 : Space n) r, max (q x) 0)≤ E+B*(∫ x, φ x) := by
  have hPhiInt : Integrable φ := hφ.integrable_of_hasCompactSupport hcφ
  let A : Space n → ℝ := fun x => φ x*(q x+B)
  have hAeq : A=(fun x => φ x*q x+φ x*B) := by funext x;dsimp only [A];ring
  have hAInt : Integrable A := by
    rw [hAeq]
    exact hpair.add (hPhiInt.mul_const B)
  have hA0 (x : Space n) : 0≤ A x := by
    by_cases hx : φ x=0
    · simp only [A,hx,zero_mul,le_refl]
    · have hl := hlower x (hsupp (subset_tsupport φ hx))
      exact mul_nonneg (hφ0 x) (by linarith only [hl])
  have hqInner : ContinuousOn (fun x => max (q x) 0) (Metric.closedBall (0 : Space n) r) :=
    (hq.mono (Metric.closedBall_subset_closedBall hrR)).sup continuousOn_const
  have hqInt : IntegrableOn (fun x => max (q x) 0) (Metric.ball (0 : Space n) r) :=
    (hqInner.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall
  have hPoint (x : Space n) (hx : x∈Metric.ball (0 : Space n) r) : max (q x) 0≤ A x := by
    have hxc := Metric.ball_subset_closedBall hx
    have hl := hlower x (Metric.closedBall_subset_closedBall hrR hxc)
    have hh : max (q x) 0≤ q x+B := max_le (le_add_of_nonneg_right hB) (by linarith only [hl])
    simpa only [A,hone x hxc,one_mul] using hh
  have hBound := integral_mono_ae hqInt hAInt.integrableOn (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hPoint x hx)
  have hWhole := setIntegral_le_integral hAInt (ae_of_all volume hA0) (s := Metric.ball (0 : Space n) r)
  have hAIntegral : (∫ x, A x)=(∫ x, φ x*q x)+B*(∫ x, φ x) := by
    rw [hAeq,integral_add hpair (hPhiInt.mul_const B),integral_mul_const]
    ring
  refine ⟨hqInt,(hBound.trans hWhole).trans ?_⟩
  rw [hAIntegral]
  exact add_le_add ((le_abs_self _).trans hPairBound) (le_refl _)

end Yau.LeafProofs.L05AutonomousAux
