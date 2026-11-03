import Yau.Proofs.F03BoundaryGeometry
import Yau.Proofs.F03BoundaryGluing

/-! Actual global coercive boundary tests for every original smooth domain. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem exists_actual_coercive_boundary_test (g : SmoothMetric M)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω) (p : M.Carrier) (hp : p ∈ frontier Ω)
    (s R : ℝ) (hs : 0 ≤ s) (hR : 0 ≤ R) :
    ∃ (a : M.Carrier) (δ c : ℝ) (k : M.Carrier → ℝ),
      0 < δ ∧ 0 < c ∧ p ∈ (extChartAt (ComplexModel n) a).source ∧
      Metric.closedBall (chartPt a p) δ ⊆ chartTarget a ∧
      SmoothFn k ∧ HasCompactSupport k ∧ k p+c=0 ∧
      (∀ x ∈ Ω, 0 ≤ k x+c) ∧
      (∀ x ∈ Ω, x ∉ chartInv a '' Metric.ball (chartPt a p) (δ/4) → s ≤ k x+c) ∧
      (∀ x ∈ Ω, x ∈ chartInv a '' Metric.ball (chartPt a p) (δ/4) →
        R ≤ k x+c-laplacian g.form (fun y => k y+c) x) := by
  obtain ⟨a,r,q,κ,δ,hpsrc,hr,hcr,hq,hcq,hκ,hδ,ht,hBp,hbound⟩ :=
    exists_actual_boundary_barrier g Ω hΩ p hp
  let B := boundaryBarrier r q κ
  let c := s+1
  let Q := R+1+s/(δ/4)^2
  have hden : 0 < (δ/4)^2 := sq_pos_of_pos (by positivity)
  have hdiv : 0 ≤ s/(δ/4)^2 := div_nonneg hs hden.le
  have hRQ : R ≤ Q := by dsimp only [Q];linarith only [hdiv]
  have hQ : 0 ≤ Q := hR.trans hRQ
  have hsc : s ≤ c := by dsimp only [c];linarith
  have hQc : Q*(δ/4)^2=(R+1)*(δ/4)^2+s := by
    dsimp only [Q]
    rw [add_mul,div_mul_cancel₀ _ hden.ne']
  have hsQ : s ≤ Q*(δ/4)^2 := by
    rw [hQc]
    have hnonneg := mul_nonneg (by linarith only [hR] : 0 ≤ R+1) hden.le
    linarith only [hnonneg]
  obtain ⟨k,hk,hkc,hkp,hk0,hks,hkL⟩ := exists_glued_nonnegative_boundary_test g.form Ω p a hpsrc
    B (boundaryBarrier_smooth hr hq κ) hBp hδ ht
    (fun z hz hzΩ => (hbound z hz hzΩ).2.1)
    (fun z hz hzΩ => (hbound z hz hzΩ).2.2.2)
    c Q s hQ hs hsc hsQ
  refine ⟨a,δ,c,k,hδ,by dsimp only [c];linarith only [hs],hpsrc,ht,hk,hkc,hkp,hk0,hks,?_⟩
  intro x hx hxinner
  exact hRQ.trans (hkL x hx hxinner)

end Yau.Proofs.F03Aux
