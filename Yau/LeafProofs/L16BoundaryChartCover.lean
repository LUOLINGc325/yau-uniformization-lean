import Yau.LeafProofs.L16DefiningFlattening

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance boundaryChartCover_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartCover_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartCover_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartCover_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartCover_thirdGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance boundaryChartCover_thirdSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance

/-- A genuine local chart has two positive buffers whose fourfold closed
    balls stay inside its source and target. -/
theorem openPartialHomeomorph_buffered_radii {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n)) {x : Space n}
    (hx : x ∈ c.source) (hcx : c x = 0) :
    ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ Metric.closedBall x (4*r) ⊆ c.source ∧
      Metric.closedBall 0 (4*q) ⊆ c.target := by
  obtain ⟨ε,hε,hS⟩ := Metric.isOpen_iff.mp c.open_source x hx
  have h0 : (0 : Space n) ∈ c.target := hcx ▸ c.map_source hx
  obtain ⟨δ,hδ,hT⟩ := Metric.isOpen_iff.mp c.open_target 0 h0
  refine ⟨ε/8,δ/8,by positivity,by positivity,?_,?_⟩
  · exact (Metric.closedBall_subset_ball (by linarith : 4*(ε/8) < ε)).trans hS
  · exact (Metric.closedBall_subset_ball (by linarith : 4*(δ/8) < δ)).trans hT

/-- Compactness of the actual smooth-domain frontier supplies finitely many
    buffered, finite-order smooth flattening charts. All geometry is selected
    before any PDE coefficients, source, or boundary data. -/
theorem smoothDomain_finite_buffered_boundary_charts {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O) :
    ∃ (e : frontier O → Space n)
      (c : frontier O → OpenPartialHomeomorph (Space n) (Space n))
      (r q : frontier O → ℝ) (s : Finset (frontier O)),
      (∀ i : frontier O, ‖e i‖ = 1 ∧ 0 < r i ∧ 0 < q i ∧
        c i i = 0 ∧ Metric.closedBall (i : Space n) (4*r i) ⊆ (c i).source ∧
        Metric.closedBall 0 (4*q i) ⊆ (c i).target ∧
        ContDiffOn ℝ 3 (c i) (c i).source ∧ ContDiffOn ℝ 3 (c i).symm (c i).target ∧
        ∀ y ∈ (c i).source,
          (y ∈ O ↔ 0 < inner ℝ (e i) (c i y)) ∧
          (y ∈ closure O ↔ 0 ≤ inner ℝ (e i) (c i y)) ∧
          (y ∈ frontier O ↔ inner ℝ (e i) (c i y) = 0)) ∧
      frontier O ⊆ ⋃ i ∈ s, Metric.ball (i : Space n) (r i) := by
  classical
  choose e c he hx hcx hc hci hFaces using fun i : frontier O =>
    smoothDomain_boundary_closed_flat_chart hO i.2
  choose r q hr hq hSource hTarget using fun i : frontier O =>
    openPartialHomeomorph_buffered_radii (c i) (hx i) (hcx i)
  have hCompact : IsCompact (frontier O) :=
    hO.2.2.1.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨s,hs⟩ := hCompact.elim_finite_subcover (fun i : frontier O => Metric.ball (i : Space n) (r i))
    (fun _ => Metric.isOpen_ball) (by
      intro x hxO
      exact mem_iUnion.mpr ⟨⟨x,hxO⟩,Metric.mem_ball_self (hr ⟨x,hxO⟩)⟩)
  refine ⟨e,c,r,q,s,?_,hs⟩
  intro i
  exact ⟨he i,hr i,hq i,hcx i,hSource i,hTarget i,hc i,hci i,hFaces i⟩

/-- Actual first, second and third derivatives of a C³ map are continuous
    on its open domain; these are the ambient derivatives used by the PDE. -/
theorem contDiffOn_three_actual_jets_continuous {n : ℕ} {V : Set (Space n)} (hV : IsOpen V)
    {f : Space n → Space n} (hf : ContDiffOn ℝ 3 f V) :
    ContinuousOn (fderiv ℝ f) V ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ f)) V ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) V := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    exact ((hf.contDiffAt (hV.mem_nhds hx)).continuousAt_fderiv (by norm_num)).continuousWithinAt
  · intro x hx
    exact (((hf.contDiffAt (hV.mem_nhds hx)).fderiv_right (m := 2) (by norm_num)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  · intro x hx
    exact ((((hf.contDiffAt (hV.mem_nhds hx)).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)).continuousWithinAt

/-- The genuine finite-order chart derivatives have a quantitative common
    bound on every compact subset of their open domain. -/
theorem compact_actual_three_jet_bound {n : ℕ} {V K : Set (Space n)} (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) {f : Space n → Space n} (hf : ContDiffOn ℝ 3 f V) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      ‖fderiv ℝ f x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ C := by
  obtain ⟨h1,h2,h3⟩ := contDiffOn_three_actual_jets_continuous hV hf
  obtain ⟨C1,hC1⟩ := hK.exists_bound_of_continuousOn (h1.mono hKV)
  obtain ⟨C2,hC2⟩ := hK.exists_bound_of_continuousOn (h2.mono hKV)
  obtain ⟨C3,hC3⟩ := hK.exists_bound_of_continuousOn (h3.mono hKV)
  refine ⟨1+|C1|+|C2|+|C3|,by positivity,?_⟩
  intro x hx
  refine ⟨(hC1 x hx).trans ?_,(hC2 x hx).trans ?_,(hC3 x hx).trans ?_⟩ <;>
    linarith [le_abs_self C1,le_abs_self C2,le_abs_self C3,abs_nonneg C1,abs_nonneg C2,abs_nonneg C3]

/-- Both directions of a buffered chart have one honest bound for all three
    actual derivatives on the corresponding closed buffers. -/
theorem buffered_chart_actual_jet_bound {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    (x : Space n) (r q : ℝ)
    (hSource : Metric.closedBall x (4*r) ⊆ c.source)
    (hTarget : Metric.closedBall 0 (4*q) ⊆ c.target) :
    ∃ C : ℝ, 0 < C ∧
      (∀ y ∈ Metric.closedBall x (4*r), ‖fderiv ℝ c y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ c) y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c)) y‖ ≤ C) ∧
      (∀ y ∈ Metric.closedBall 0 (4*q), ‖fderiv ℝ c.symm y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ c.symm) y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ c.symm)) y‖ ≤ C) := by
  obtain ⟨C1,hC1,h1⟩ := compact_actual_three_jet_bound c.open_source (isCompact_closedBall x (4*r)) hSource hc
  obtain ⟨C2,hC2,h2⟩ := compact_actual_three_jet_bound c.open_target (isCompact_closedBall 0 (4*q)) hTarget hci
  refine ⟨C1+C2,by positivity,?_,?_⟩
  · intro y hy
    obtain ⟨hD,hDD,hDDD⟩ := h1 y hy
    exact ⟨by linarith,by linarith,by linarith⟩
  · intro y hy
    obtain ⟨hD,hDD,hDDD⟩ := h2 y hy
    exact ⟨by linarith,by linarith,by linarith⟩

/-- Mean value estimates on a genuine convex chart buffer control the map
    and its first two derivatives by its actual three-jet bound. -/
theorem chart_actual_two_jet_lipschitz {n : ℕ} {V K : Set (Space n)} (hV : IsOpen V)
    (hK : Convex ℝ K) (hKV : K ⊆ V) {f : Space n → Space n} (hf : ContDiffOn ℝ 3 f V)
    {C : ℝ} (hBound : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ C)
    {x y : Space n} (hx : x ∈ K) (hy : y ∈ K) :
    ‖f x-f y‖ ≤ C*‖x-y‖ ∧
      ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ C*‖x-y‖ ∧
      ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ C*‖x-y‖ := by
  have hD (z : Space n) (hz : z ∈ K) : ContDiffAt ℝ 3 f z := hf.contDiffAt (hV.mem_nhds (hKV hz))
  refine ⟨?_,?_,?_⟩
  · exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hD z hz).differentiableAt (by norm_num)) (fun z hz => (hBound z hz).1) hK hy hx
  · exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hD z hz).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
      (fun z hz => (hBound z hz).2.1) hK hy hx
  · exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (((hD z hz).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
        (by norm_num)).differentiableAt (by norm_num)) (fun z hz => (hBound z hz).2.2) hK hy hx

end Yau.LeafProofs.L16Aux
