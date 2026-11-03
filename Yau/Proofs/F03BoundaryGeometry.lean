import Yau.Proofs.F03BoundaryDefiningTests
import Yau.Proofs.F03BoundaryBarrier

/-! The actual defining functions give a finite strict scalar boundary barrier. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem exists_actual_boundary_barrier (g : SmoothMetric M)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω) (p : M.Carrier) (hp : p ∈ frontier Ω) :
    ∃ (a : M.Carrier) (r q : M.Carrier → ℝ) (κ δ : ℝ),
      p ∈ (extChartAt (ComplexModel n) a).source ∧
      SmoothFn r ∧ HasCompactSupport r ∧ SmoothFn q ∧ HasCompactSupport q ∧
      0 < κ ∧ 0 < δ ∧ Metric.closedBall (chartPt a p) δ ⊆ chartTarget a ∧
      boundaryBarrier r q κ p=0 ∧
      ∀ z ∈ Metric.closedBall (chartPt a p) δ, chartInv a z ∈ Ω →
        0 ≤ r (chartInv a z) ∧
        ‖z-chartPt a p‖^2 ≤ boundaryBarrier r q κ (chartInv a z) ∧
        boundaryBarrier r q κ (chartInv a z) ≤ r (chartInv a z)+‖z-chartPt a p‖^2 ∧
        1 ≤ -laplacian g.form (boundaryBarrier r q κ) (chartInv a z) := by
  obtain ⟨a,r,q,W,hpsrc,hr,hcr,hq,hcq,hW,hpW,hWt,hrzero,hqzero,hGrad,hRpos,hQdist⟩ :=
    exists_boundary_defining_tests g.form Ω hΩ p hp
  let z₀ := chartPt a p
  have hinv : chartInv a z₀=p := (extChartAt (ComplexModel n) a).left_inv hpsrc
  let b := scalarGradientPair g.form r r p/2
  have hb : 0 < b := half_pos hGrad
  let G : ComplexVector n → ℝ := inChart a (scalarGradientPair g.form r r)
  have hGc : ContinuousAt G z₀ :=
    ((smoothFn_scalarGradientPair g hr hr) a).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds (hWt hpW))
  have hbG : b < G z₀ := by
    simpa only [G,inChart,hinv] using half_lt_self hGrad
  have hOuterEvent : ∀ᶠ z in 𝓝 z₀, z ∈ W ∧ b < G z := by
    filter_upwards [hW.mem_nhds hpW,hGc.eventually (eventually_gt_nhds hbG)] with z hz hGz
    exact ⟨hz,hGz⟩
  obtain ⟨R,hR,hOuter⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hOuterEvent
  have hRt : Metric.closedBall z₀ R ⊆ chartTarget a := fun z hz => hWt (hOuter hz).1
  let K := chartInv a '' Metric.closedBall z₀ R
  have hKc : IsCompact K := (isCompact_closedBall z₀ R).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hRt)
  obtain ⟨Cr,hCr⟩ := hKc.bddAbove_image
    (continuous_of_smoothFn (smoothFn_laplacian g hr)).continuousOn
  obtain ⟨Cq,hCq⟩ := hKc.bddAbove_image
    (continuous_of_smoothFn (smoothFn_laplacian g hq)).continuousOn
  let A := max 0 (max Cr Cq)
  have hA : 0 ≤ A := le_max_left _ _
  have hLr : ∀ y ∈ K, laplacian g.form r y ≤ A := by
    intro y hy
    exact (hCr ⟨y,hy,rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hLq : ∀ y ∈ K, laplacian g.form q y ≤ A := by
    intro y hy
    exact (hCq ⟨y,hy,rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  let κ := (2*A+1)/b
  have hκ : 0 < κ := div_pos (by linarith only [hA]) hb
  have hκb : κ*b=2*A+1 := by dsimp only [κ];field_simp
  let η := 1/(4*κ)
  have hη : 0 < η := by dsimp only [η];positivity
  have hrc : ContinuousAt (fun z => |r (chartInv a z)|) z₀ :=
    ((hr a).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds (hWt hpW))).abs
  have hzeroSmall : |r (chartInv a z₀)| < η := by simpa only [hinv,hrzero,abs_zero] using hη
  have hInnerEvent : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ R ∧ |r (chartInv a z)| < η := by
    filter_upwards [Metric.ball_mem_nhds z₀ hR,hrc.eventually (eventually_lt_nhds hzeroSmall)] with z hz hsmall
    exact ⟨hz,hsmall⟩
  obtain ⟨δ,hδ,hInner⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hInnerEvent
  have hδR : Metric.closedBall z₀ δ ⊆ Metric.closedBall z₀ R :=
    fun z hz => Metric.ball_subset_closedBall (hInner hz).1
  refine ⟨a,r,q,κ,δ,hpsrc,hr,hcr,hq,hcq,hκ,hδ,hδR.trans hRt,
    boundaryBarrier_at_boundary κ p hrzero hqzero,?_⟩
  intro z hz hzΩ
  have hzR := hδR hz
  have hzW := (hOuter hzR).1
  have hrz : 0 ≤ r (chartInv a z) := (hRpos z hzW hzΩ).le
  have hqz := hQdist z hzW
  have hsmall := (hInner hz).2
  have hsmall' : |r (chartInv a z)| * (4*κ) < 1 := (lt_div_iff₀ (by positivity : 0 < 4*κ)).mp hsmall
  have hmul := mul_le_mul_of_nonneg_left (le_abs_self (r (chartInv a z))) hκ.le
  have hκr : 2*κ*r (chartInv a z) ≤ 1 := by nlinarith only [hsmall',hmul]
  have hκrHalf : κ*r (chartInv a z) ≤ 1/2 := by linarith only [hκr]
  have hLow := boundaryBarrier_lower (r := r) (q := q) κ (chartInv a z) hrz hκrHalf
  have hUp : boundaryBarrier r q κ (chartInv a z) ≤ r (chartInv a z)+q (chartInv a z) := by
    have hnonneg := mul_nonneg hκ.le (sq_nonneg (r (chartInv a z)))
    unfold boundaryBarrier
    nlinarith only [hnonneg]
  have hGradz : b ≤ scalarGradientPair g.form r r (chartInv a z) := (hOuter hzR).2.le
  have hNeg := boundaryBarrier_neg_laplacian g.form hr hq κ A b (chartInv a z) hκ.le hA hrz hκr
    (hLr _ ⟨z,hzR,rfl⟩) (hLq _ ⟨z,hzR,rfl⟩) hGradz (by rw [hκb])
  rw [hqz] at hLow hUp
  exact ⟨hrz,by linarith only [hLow,hrz],hUp,hNeg⟩

end Yau.Proofs.F03Aux
