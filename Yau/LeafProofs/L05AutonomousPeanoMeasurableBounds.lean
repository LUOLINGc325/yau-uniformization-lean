import Yau.LeafProofs.L05AutonomousPeanoMeasurableCountable

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem peano_good_direction_bound {n : ℕ} {D : Set (Point n)} {u : Point n → ℝ}
    (hu : Continuous u) {G : Point n → (Space n →L[ℝ] ℝ)} {M h0 : ℝ}
    (hh0 : 0 < h0)
    (hFinite : ∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h ≠ 0 → |h| < h0 →
      ∀ p ∈ D, |autoSecond u e h p| ≤ M)
    {p : Point n} (hpD : p ∈ D) (hp : p ∈ peanoCountableGoodSet u G)
    (e : Space n) (he : ‖e‖=1) :
    |autoBilinearMap n (peanoMeasurableHessian u p) e e| ≤ M := by
  have hLimit := peano_second_limit (peano_littleO_of_countable hu hp) e
  have hSmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < h0 :=
    (eventually_lt_nhds hh0).filter_mono nhdsWithin_le_nhds
  have hBound : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), |autoSecond u e h p| ≤ M := by
    filter_upwards [self_mem_nhdsWithin,hSmall] with h hh hs
    have hhPos : 0 < h := hh
    exact hFinite e he h (ne_of_gt hhPos) (by simpa only [abs_of_pos hhPos] using hs) p hpD
  exact le_of_tendsto ((continuous_abs.tendsto _).comp hLimit) hBound

theorem peano_good_hessian_bound {n : ℕ} {D : Set (Point n)} {u : Point n → ℝ}
    (hu : Continuous u) {G : Point n → (Space n →L[ℝ] ℝ)} {M h0 : ℝ}
    (hM : 0 ≤ M) (hh0 : 0 < h0)
    (hFinite : ∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h ≠ 0 → |h| < h0 →
      ∀ p ∈ D, |autoSecond u e h p| ≤ M)
    {p : Point n} (hpD : p ∈ D) (hp : p ∈ peanoCountableGoodSet u G) :
    ‖peanoMeasurableHessian u p‖ ≤ (4*(n : ℝ)+1)*M := by
  let H := peanoMeasurableHessian u p
  have hDirection (e : Space n) (he : ‖e‖=1) : |autoBilinearMap n H e e| ≤ M :=
    peano_good_direction_bound hu hh0 hFinite hpD hp e he
  have hDiag (i : Yau.RIdx n) : |(H : Mat n) i i| ≤ M := by
    rw [← autoBilinearMap_realVec]
    exact hDirection (Yau.realVec i) (auto_realVec_norm i)
  have hEntry (i j : Yau.RIdx n) : |(H : Mat n) i j| ≤ 2*M := by
    by_cases hij : i=j
    · subst j
      exact (hDiag i).trans (by linarith only [hM])
    have hPair := hDirection (autoPairDirection i j) (autoPairDirection_norm hij)
    have hIdentity := peano_bilinear_pair (autoBilinearMap n H)
      (autoBilinearMap_symmetric H) i j
    simp only [autoBilinearMap_realVec] at hIdentity
    rw [hIdentity] at hPair
    have hPi := abs_le.mp (hDiag i)
    have hPj := abs_le.mp (hDiag j)
    have hP := abs_le.mp hPair
    exact abs_le.mpr ⟨by linarith only [hPi.2,hPj.2,hP.1],
      by linarith only [hPi.1,hPj.1,hP.2]⟩
  calc
    _ ≤ (2*n : ℝ)*(2*M) := auto_matrix_norm_le_entry_bound H (by positivity) hEntry
    _ ≤ _ := by nlinarith only [hM]

end Yau.LeafProofs.L05AutonomousAux
