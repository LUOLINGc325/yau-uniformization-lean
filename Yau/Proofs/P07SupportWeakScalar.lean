import Yau.Proofs.P07SupportWeakMean

noncomputable section
open Filter Set Metric InnerProductSpace Laplacian
open scoped Topology ContDiff
namespace Yau.NodeProofs.P07Aux.SupportWeak

/-- No sign condition on the frozen numerical right side is needed. -/
theorem circleSupermean_of_lowerTests_const
    {g : ℂ → ℝ} (hg : ContinuousOn g (closedBall (0 : ℂ) 1))
    {b : ℝ} (htest : ScalarLowerTestUpperOn (ball 0 1) g (4 * b)) :
    Real.circleAverage g 0 1 ≤ g 0 + b := by
  let k : ℂ → ℝ := fun z => g z - b * ‖z‖ ^ 2
  have hnorm : ContDiff ℝ 2 (fun z : ℂ => b * ‖z‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hk : ContinuousOn k (closedBall (0 : ℂ) 1) := hg.sub hnorm.continuous.continuousOn
  have hktest : ScalarLowerTestUpperOn (ball 0 1) k 0 := by
    intro z hz q hq hqz hqk
    let Q : ℂ → ℝ := fun ζ => q ζ + b * ‖ζ‖ ^ 2
    have hQ : ContDiffAt ℝ 2 Q z := hq.add hnorm.contDiffAt
    have hQz : Q z = g z := by dsimp [Q, k] at *; linarith
    have hQg : ∀ᶠ ζ in 𝓝 z, Q ζ ≤ g ζ := by
      filter_upwards [hqk] with ζ hζ
      dsimp [Q, k] at *
      linarith
    have hbound := htest z hz Q hQ hQz hQg
    have hadd := hq.laplacian_add hnorm.contDiffAt
    have hmul := laplacian_smul b ((contDiff_norm_sq ℝ).contDiffAt (x := z))
    have hLap : complexLap Q z = complexLap q z + 4 * b := by
      change complexLap Q z = complexLap q z + complexLap (fun ζ : ℂ => b * ‖ζ‖ ^ 2) z at hadd
      have hm : complexLap (fun ζ : ℂ => b * ‖ζ‖ ^ 2) z =
          b * complexLap (fun ζ : ℂ => ‖ζ‖ ^ 2) z := hmul
      rw [hm, complexLap_norm_sq] at hadd
      linarith
    rw [hLap] at hbound
    linarith
  have hmean := circleSupermean_of_lowerTests hk hktest
  have hgi : CircleIntegrable g 0 1 :=
    (hg.mono (by simpa only [abs_one] using
      (sphere_subset_closedBall : sphere (0 : ℂ) 1 ⊆ closedBall 0 1))).circleIntegrable'
  have hni : CircleIntegrable (fun z : ℂ => b * ‖z‖ ^ 2) 0 1 :=
    hnorm.continuous.continuousOn.circleIntegrable'
  have hnmean : Real.circleAverage (fun z : ℂ => b * ‖z‖ ^ 2) 0 1 = b := by
    apply Real.circleAverage_const_on_circle
    intro z hz
    have hz' : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right, abs_one] using hz
    simp only [hz', one_pow, mul_one]
  have hsub := Real.circleAverage_sub hgi hni
  change Real.circleAverage k 0 1 = Real.circleAverage g 0 1 -
    Real.circleAverage (fun z : ℂ => b * ‖z‖ ^ 2) 0 1 at hsub
  rw [hsub, hnmean] at hmean
  have hk0 : k 0 = g 0 := by simp [k]
  rw [hk0] at hmean
  linarith

end Yau.NodeProofs.P07Aux.SupportWeak
