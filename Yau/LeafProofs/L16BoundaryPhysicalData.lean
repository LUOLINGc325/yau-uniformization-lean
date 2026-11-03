import Yau.LeafProofs.L16BoundaryModelData

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance boundaryPhysicalData_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryPhysicalData_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryPhysicalData_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryPhysicalData_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryPhysicalData_thirdGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryPhysicalData_thirdSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryPhysicalData_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance boundaryPhysicalData_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Actual spatial Lipschitz pullback of a parabolic Holder field on its
    given spatial domain. No extension outside that domain is assumed. -/
theorem holderBound_spatial_lipschitz_pullback {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {α T C L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L) {S K : Set (Space n)}
    (ψ : Space n → Space n) (hMap : MapsTo ψ S K)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖ψ x-ψ y‖ ≤ L*‖x-y‖)
    {f : Point n → E} (hf : HolderBound α (cylinder K 0 T) f C) :
    HolderBound α (cylinder S 0 T) (fun p => f (ψ p.1,p.2)) (C*(1+L^α)) := by
  have hPow : 0 ≤ L^α := Real.rpow_nonneg hL _
  have hFactor : 1 ≤ 1+L^α := le_add_of_nonneg_right hPow
  have hPowFactor : L^α ≤ 1+L^α := by linarith
  have hMapP (p : Point n) (hp : p ∈ cylinder S 0 T) : (ψ p.1,p.2) ∈ cylinder K 0 T :=
    ⟨hMap hp.1,hp.2⟩
  refine ⟨mul_nonneg hf.1 (by positivity),?_,?_⟩
  · intro p hp
    exact (hf.2.1 _ (hMapP p hp)).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hFactor hf.1)
  · intro p hp q hq
    have hSpace : ‖ψ p.1-ψ q.1‖^α ≤ L^α*‖p.1-q.1‖^α := by
      calc
        _ ≤ (L*‖p.1-q.1‖)^α := Real.rpow_le_rpow (norm_nonneg _) (hLip _ hp.1 _ hq.1) hα
        _ = _ := Real.mul_rpow hL (norm_nonneg _)
    have hW : holderWeight α (ψ p.1,p.2) (ψ q.1,q.2) ≤ (1+L^α)*holderWeight α p q := by
      dsimp only [holderWeight]
      have hD0 := Real.rpow_nonneg (norm_nonneg (p.1-q.1)) α
      have hT0 := Real.rpow_nonneg (abs_nonneg (p.2-q.2)) (α/2)
      calc
        _ ≤ L^α*‖p.1-q.1‖^α+|p.2-q.2|^(α/2) := add_le_add hSpace le_rfl
        _ ≤ (1+L^α)*‖p.1-q.1‖^α+(1+L^α)*|p.2-q.2|^(α/2) := add_le_add
          (mul_le_mul_of_nonneg_right hPowFactor hD0)
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hFactor hT0)
        _ = _ := by ring
    exact (hf.2.2 _ (hMapP p hp) _ (hMapP q hq)).trans
      ((mul_le_mul_of_nonneg_left hW hf.1).trans_eq (by ring))

/-- Around a centered chart point, a smaller actual source buffer maps into
    any prescribed positive target ball. -/
theorem openPartialHomeomorph_source_small_image {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n)) {x : Space n}
    (hx : x ∈ c.source) (hcx : c x = 0) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall x (4*δ) ⊆ c.source ∧
      MapsTo c (Metric.closedBall x (4*δ)) (Metric.ball 0 R) := by
  have hOpen : IsOpen (c.source∩(c : Space n → Space n) ⁻¹' Metric.ball (0 : Space n) R) := c.isOpen_inter_preimage Metric.isOpen_ball
  have hxBall : c x ∈ Metric.ball (0 : Space n) R := by
    rw [hcx]
    exact Metric.mem_ball_self hR
  have hxOpen : x ∈ c.source∩(c : Space n → Space n) ⁻¹' Metric.ball (0 : Space n) R := ⟨hx,hxBall⟩
  obtain ⟨ε,hε,hεSub⟩ := Metric.isOpen_iff.mp hOpen x hxOpen
  have hSub : Metric.closedBall x (4*(ε/8)) ⊆ c.source∩(c : Space n → Space n) ⁻¹' Metric.ball (0 : Space n) R :=
    (Metric.closedBall_subset_ball (by linarith : 4*(ε/8) < ε)).trans hεSub
  exact ⟨ε/8,by positivity,fun y hy => (hSub hy).1,fun y hy => (hSub hy).2⟩

/-- Near an actual boundary point, original Schauder data have a uniform
    original value/gradient Holder bound on a genuine physical neighbourhood.
All constants and neighbourhoods are fixed before the datum. -/
theorem smoothDomain_boundary_data_low_holder {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {x : Space n} (hx : x ∈ frontier O) {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ (u : Point n → ℝ) P,
      SchauderBound α (cylinder (closure O) 0 T) u P →
      HolderBound α (cylinder (closure O∩Metric.closedBall x δ) 0 T)
        (fun p => (u p,spatialD u p)) (A*P) := by
  obtain ⟨e,c,q,A,he,hxc,hcx,hq,hA,hTarget,hc,hci,hFaces,hModel⟩ :=
    smoothDomain_boundary_model_data_low_holder hO hx hα hα1 hT
  obtain ⟨δ,hδ,hSource,hImage⟩ := openPartialHomeomorph_source_small_image c hxc hcx
    (by positivity : 0 < q/2)
  let S := closure O∩Metric.closedBall x δ
  let K := {y : Space n | 0 ≤ inner ℝ e y}∩Metric.closedBall 0 (q/2)
  have hSmall : Metric.closedBall x δ ⊆ Metric.closedBall x (4*δ) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hSLarge : S ⊆ Metric.closedBall x (4*δ) := fun y hy => hSmall hy.2
  have hMap : MapsTo c S K := by
    intro y hy
    exact ⟨(hFaces y (hSource (hSLarge hy))).2.1.mp hy.1,
      Metric.ball_subset_closedBall (hImage (hSLarge hy))⟩
  obtain ⟨B,hB,hBound⟩ := compact_actual_three_jet_bound c.open_source
    (isCompact_closedBall x (4*δ)) hSource hc
  have hLip : ∀ y ∈ S, ∀ z ∈ S, ‖c y-c z‖ ≤ B*‖y-z‖ := by
    intro y hy z hz
    exact (chart_actual_two_jet_lipschitz c.open_source (convex_closedBall x (4*δ)) hSource hc
      hBound (hSLarge hy) (hSLarge hz)).1
  refine ⟨δ,A*(1+B^α),hδ,by positivity,?_⟩
  intro u P hu
  have hh := holderBound_spatial_lipschitz_pullback hα.le hB.le c hMap hLip (hModel u P hu)
  have hBudget : (A*P)*(1+B^α) = (A*(1+B^α))*P := by ring
  rw [hBudget] at hh
  apply holderBound_congr_on hh
  intro p hp
  change (u (c.symm (c p.1),p.2),spatialD u (c.symm (c p.1),p.2)) = (u p,spatialD u p)
  rw [c.left_inv (hSource (hSLarge hp.1))]

end Yau.LeafProofs.L16Aux
