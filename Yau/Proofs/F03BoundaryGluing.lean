import Yau.Proofs.F03ChartCutoff
import Yau.Proofs.F03BoundaryBarrier
import Yau.LeafProofs.L22Locality

/-! Actual global nonnegative boundary comparisons from a strict local barrier. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem chartInv_image_ball_open (a : M.Carrier) (z₀ : ComplexVector n)
    {d : ℝ} (ht : Metric.ball z₀ d ⊆ chartTarget a) :
    IsOpen (chartInv a '' Metric.ball z₀ d) := by
  change IsOpen ((chartAt (ComplexVector n) a).symm '' Metric.ball z₀ d)
  apply (chartAt (ComplexVector n) a).symm.isOpen_image_of_subset_source Metric.isOpen_ball
  intro z hz
  have hz' := ht hz
  rw [chartTarget,extChartAt_target] at hz'
  exact hz'.1

theorem exists_glued_nonnegative_boundary_test (g : HermitianField M)
    (Ω : Set M.Carrier) (p a : M.Carrier) (hpsrc : p ∈ (extChartAt (ComplexModel n) a).source)
    (B : M.Carrier → ℝ) (hB : SmoothFn B) (hBp : B p=0)
    {δ : ℝ} (hδ : 0 < δ) (ht : Metric.closedBall (chartPt a p) δ ⊆ chartTarget a)
    (hBd : ∀ z ∈ Metric.closedBall (chartPt a p) δ, chartInv a z ∈ Ω →
      ‖z-chartPt a p‖^2 ≤ B (chartInv a z))
    (hBL : ∀ z ∈ Metric.closedBall (chartPt a p) δ, chartInv a z ∈ Ω →
      1 ≤ -laplacian g B (chartInv a z))
    (c Q s : ℝ) (hQ : 0 ≤ Q) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hsQ : s ≤ Q*(δ/4)^2) :
    ∃ k : M.Carrier → ℝ, SmoothFn k ∧ HasCompactSupport k ∧ k p+c=0 ∧
      (∀ x ∈ Ω, 0 ≤ k x+c) ∧
      (∀ x ∈ Ω, x ∉ chartInv a '' Metric.ball (chartPt a p) (δ/4) → s ≤ k x+c) ∧
      (∀ x ∈ Ω, x ∈ chartInv a '' Metric.ball (chartPt a p) (δ/4) →
        Q ≤ k x+c-laplacian g (fun y => k y+c) x) := by
  let z₀ := chartPt a p
  obtain ⟨χ,hχ,hcχ,hχbounds,hχsupp,hχone⟩ := exists_compact_chart_cutoff a z₀ hδ ht
  let k : M.Carrier → ℝ := fun x => χ x*(Q*B x-c)
  have hk : SmoothFn k := smoothFn_mul hχ
    (smoothFn_sub (smoothFn_mul (smoothFn_const Q) hB) (smoothFn_const c))
  have hkc : HasCompactSupport k := hcχ.mul_right
  have hinv : chartInv a z₀=p := (extChartAt (ComplexModel n) a).left_inv hpsrc
  have hχp : χ p=1 := by
    have hpball : z₀ ∈ Metric.closedBall z₀ (δ/2) := Metric.mem_closedBall_self (by positivity)
    simpa only [hinv] using hχone z₀ hpball
  have hc : 0 ≤ c := hs.trans hsc
  have hballhalf : Metric.ball z₀ (δ/2) ⊆ Metric.closedBall z₀ δ := by
    intro z hz
    exact (Metric.mem_ball.mp hz).le.trans (by linarith only [hδ])
  have hballquarter : Metric.ball z₀ (δ/4) ⊆ Metric.ball z₀ (δ/2) :=
    Metric.ball_subset_ball (by linarith only [hδ])
  have hpos : ∀ x ∈ Ω, χ x ≠ 0 → 0 ≤ B x := by
    intro x hx hn
    obtain ⟨z,hz,rfl⟩ := hχsupp (subset_closure hn)
    exact (sq_nonneg ‖z-z₀‖).trans (hBd z hz hx)
  have hEq : ∀ x, k x+c=(1-χ x)*c+χ x*(Q*B x) := by
    intro x
    dsimp only [k]
    ring
  refine ⟨k,hk,hkc,by simp only [k,hχp,hBp,mul_zero,zero_sub,one_mul,neg_add_cancel],?_,?_,?_⟩
  · intro x hx
    by_cases hn : χ x=0
    · simp only [k,hn,zero_mul,zero_add]
      exact hc
    · rw [hEq]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hχbounds x).2) hc)
        (mul_nonneg (hχbounds x).1 (mul_nonneg hQ (hpos x hx hn)))
  · intro x hx hout
    by_cases hn : χ x=0
    · simpa only [k,hn,zero_mul,zero_add] using hsc
    obtain ⟨z,hz,hzx⟩ := hχsupp (subset_closure hn)
    have hzout : z ∉ Metric.ball z₀ (δ/4) := fun hzsmall => hout ⟨z,hzsmall,hzx⟩
    have hnorm : δ/4 ≤ ‖z-z₀‖ := by
      simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hzout
    have hsquare : (δ/4)^2 ≤ ‖z-z₀‖^2 := sq_le_sq₀ (by positivity) (norm_nonneg _) |>.mpr hnorm
    have hQB : s ≤ Q*B x := hsQ.trans
      ((mul_le_mul_of_nonneg_left hsquare hQ).trans
        (mul_le_mul_of_nonneg_left (by simpa only [hzx] using hBd z hz (hzx.symm ▸ hx)) hQ))
    rw [hEq]
    have hmix := add_le_add (mul_le_mul_of_nonneg_left hsc (sub_nonneg.mpr (hχbounds x).2))
      (mul_le_mul_of_nonneg_left hQB (hχbounds x).1)
    nlinarith only [hmix]
  · intro x hx hxinner
    obtain ⟨z,hz,hzx⟩ := hxinner
    have hzhalf := hballquarter hz
    have hUopen := chartInv_image_ball_open a z₀ (hballhalf.trans ht)
    have hUmem : x ∈ chartInv a '' Metric.ball z₀ (δ/2) := ⟨z,hzhalf,hzx⟩
    have hlocal : (fun y => k y+c) =ᶠ[𝓝 x] (fun y => Q*B y) := by
      filter_upwards [hUopen.mem_nhds hUmem] with y hy
      obtain ⟨w,hw,rfl⟩ := hy
      have hχw := hχone w (Metric.ball_subset_closedBall hw)
      dsimp only [k]
      rw [hχw,one_mul]
      ring
    have hlap : laplacian g (fun y => k y+c) x=Q*laplacian g B x := by
      unfold laplacian
      rw [LeafProofs.L22Aux.levi_congr_of_eventuallyEq hlocal]
      exact laplacian_const_mul g hB Q x
    have hxB : 0 ≤ B x := by
      have hdist := hBd z (hballhalf hzhalf) (hzx.symm ▸ hx)
      exact (sq_nonneg _).trans (by simpa only [hzx] using hdist)
    have hxL : 1 ≤ -laplacian g B x := by
      simpa only [hzx] using hBL z (hballhalf hzhalf) (hzx.symm ▸ hx)
    rw [hlap,hlocal.eq_of_nhds]
    have hmul := mul_le_mul_of_nonneg_left hxL hQ
    have hBmul := mul_nonneg hQ hxB
    nlinarith only [hmul,hBmul]

end Yau.Proofs.F03Aux
