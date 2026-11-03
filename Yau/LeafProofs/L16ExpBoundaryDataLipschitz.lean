import Yau.LeafProofs.L16ExpBoundaryData
import Yau.LeafProofs.L16DefiningFlattening
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius NNReal

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- A compact convex patch controls a fixed smooth datum using only its
within-set smoothness, including the time end faces. -/
theorem fixed_data_locally_lipschitz_interior {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) {T : ℝ} {g : Point n → ℝ}
    (hg : ContDiffOn ℝ ∞ g (cylinder (closure O) 0 T))
    {z : Point n} (hz : z ∈ cylinder (closure O) 0 T) (hzO : z.1 ∈ O) :
    ∃ K : ℝ≥0, ∃ S ∈ 𝓝[cylinder (closure O) 0 T] z, LipschitzOnWith K g S := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hzO)
  let Kset : Set (Point n) := Metric.closedBall z.1 (r/2) ×ˢ Icc 0 T
  have hKQ : Kset ⊆ cylinder (closure O) 0 T := by
    intro p hp
    exact ⟨subset_closure (hball ((Metric.closedBall_subset_ball (by linarith)) hp.1)),hp.2⟩
  have hCompact : IsCompact Kset := (isCompact_closedBall _ _).prod isCompact_Icc
  have hConvex : Convex ℝ Kset := (convex_closedBall _ _).prod (convex_Icc _ _)
  obtain ⟨K,hLip⟩ := (hg.mono hKQ).exists_lipschitzOnWith (by simp) hConvex hCompact
  let S : Set (Point n) := (Metric.ball z.1 (r/2) ×ˢ univ) ∩ cylinder (closure O) 0 T
  refine ⟨K,S,?_,hLip.mono ?_⟩
  · apply mem_nhdsWithin.mpr
    exact ⟨Metric.ball z.1 (r/2) ×ˢ univ,Metric.isOpen_ball.prod isOpen_univ,
      ⟨Metric.mem_ball_self (by positivity),mem_univ _⟩,subset_rfl⟩
  · intro p hp
    exact ⟨Metric.ball_subset_closedBall hp.1.1,hp.2.2⟩

/-- A genuine closed-face flattening chart transports the datum to a convex
compact half-ball. No ambient differentiability of g on the boundary is used. -/
theorem fixed_data_locally_lipschitz_flat_chart {n : ℕ} {O : Set (Space n)}
    {T : ℝ} {g : Point n → ℝ}
    (hg : ContDiffOn ℝ ∞ g (cylinder (closure O) 0 T))
    {z : Point n} (hz : z ∈ cylinder (closure O) 0 T)
    (e : Space n) (c : OpenPartialHomeomorph (Space n) (Space n))
    (hzS : z.1 ∈ c.source) (hcz : c z.1 = 0)
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    (hFace : ∀ y ∈ c.source, y ∈ closure O ↔ 0 ≤ inner ℝ e (c y)) :
    ∃ K : ℝ≥0, ∃ S ∈ 𝓝[cylinder (closure O) 0 T] z, LipschitzOnWith K g S := by
  have hzeroT : (0 : Space n) ∈ c.target := hcz ▸ c.map_source hzS
  obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hzeroT)
  let r : ℝ := δ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hRT : Metric.closedBall (0 : Space n) r ⊆ c.target :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hδT
  let Kspace : Set (Space n) := Metric.closedBall 0 r ∩ {y | 0 ≤ inner ℝ e y}
  let Kset : Set (Point n) := Kspace ×ˢ Icc 0 T
  have hHalfClosed : IsClosed {y : Space n | 0 ≤ inner ℝ e y} :=
    isClosed_le continuous_const (innerSL ℝ e).continuous
  have hHalfConvex : Convex ℝ {y : Space n | 0 ≤ inner ℝ e y} :=
    (convex_Ici (0 : ℝ)).linear_preimage (innerSL ℝ e).toLinearMap
  have hCompact : IsCompact Kset :=
    ((isCompact_closedBall _ _).inter_right hHalfClosed).prod isCompact_Icc
  have hConvex : Convex ℝ Kset := ((convex_closedBall _ _).inter hHalfConvex).prod (convex_Icc _ _)
  have hMap : MapsTo (fun p : Point n => (c.symm p.1,p.2)) Kset (cylinder (closure O) 0 T) := by
    intro p hp
    have hpT := hRT hp.1.1
    have hpS := c.map_target hpT
    refine ⟨(hFace _ hpS).mpr ?_,hp.2⟩
    simpa only [c.right_inv hpT,Set.mem_setOf_eq] using hp.1.2
  have hMapSmooth : ContDiffOn ℝ 1 (fun p : Point n => (c.symm p.1,p.2)) Kset :=
    (((hci.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).comp contDiffOn_fst
      (fun p hp => hRT hp.1.1)).prodMk contDiffOn_snd)
  have hPull : ContDiffOn ℝ 1 (fun p : Point n => g (c.symm p.1,p.2)) Kset :=
    (hg.of_le (by simp)).comp hMapSmooth hMap
  obtain ⟨K₀,hLipPull⟩ := hPull.exists_lipschitzOnWith (by norm_num) hConvex hCompact
  have hcAt : ContDiffAt ℝ 1 c z.1 := (hc.contDiffAt (c.open_source.mem_nhds hzS)).of_le (by norm_num)
  obtain ⟨K₁,V,hV,hLipC⟩ := hcAt.exists_lipschitzOnWith
  have hImage : ∀ᶠ y in 𝓝 z.1, c y ∈ Metric.ball 0 r := hcAt.continuousAt.eventually (by
    rw [hcz]
    exact Metric.ball_mem_nhds _ hr)
  have hAll : ∀ᶠ y in 𝓝 z.1, y ∈ V ∧ y ∈ c.source ∧ c y ∈ Metric.ball 0 r := by
    filter_upwards [hV,c.open_source.mem_nhds hzS,hImage] with y hyV hyS hyI
    exact ⟨hyV,hyS,hyI⟩
  obtain ⟨ε,hε,hεAll⟩ := Metric.eventually_nhds_iff.mp hAll
  let S : Set (Point n) := (Metric.ball z.1 ε ×ˢ univ) ∩ cylinder (closure O) 0 T
  have hFst : LipschitzOnWith K₁ (fun p : Point n => c p.1) S := by
    simpa only [mul_one,Function.comp_def] using hLipC.comp
      (LipschitzWith.prod_fst.lipschitzOnWith (s := S))
      (fun p hp => (hεAll hp.1.1).1)
  have hJoint := hFst.prodMk (LipschitzWith.prod_snd.lipschitzOnWith (s := S))
  have hJointMap : MapsTo (fun p : Point n => (c p.1,p.2)) S Kset := by
    intro p hp
    have hAllp := hεAll hp.1.1
    exact ⟨⟨Metric.ball_subset_closedBall hAllp.2.2,(hFace _ hAllp.2.1).mp hp.2.1⟩,hp.2.2⟩
  have hComp := hLipPull.comp hJoint hJointMap
  refine ⟨K₀*max K₁ 1,S,?_,?_⟩
  · apply mem_nhdsWithin.mpr
    exact ⟨Metric.ball z.1 ε ×ˢ univ,Metric.isOpen_ball.prod isOpen_univ,
      ⟨Metric.mem_ball_self hε,mem_univ _⟩,subset_rfl⟩
  · intro p hp q hq
    simpa only [Function.comp_def,c.left_inv (hεAll hp.1.1).2.1,
      c.left_inv (hεAll hq.1.1).2.1] using hComp hp hq

/-- Fixed smooth data on a smooth bounded domain are Lipschitz on the closed
cylinder, with its actual product metric. Disconnected domains are allowed. -/
theorem smoothDomain_closed_cylinder_lipschitz {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {T : ℝ} {g : Point n → ℝ}
    (hg : ContDiffOn ℝ ∞ g (cylinder (closure O) 0 T)) :
    ∃ K : ℝ≥0, LipschitzOnWith K g (cylinder (closure O) 0 T) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hO.2.2.1.prod isCompact_Icc)
  intro z hz
  by_cases hzO : z.1 ∈ O
  · exact fixed_data_locally_lipschitz_interior hO.1 hg hz hzO
  · have hzF : z.1 ∈ frontier O := ⟨hz.1,by simpa only [hO.1.interior_eq] using hzO⟩
    obtain ⟨e,c,he,hzS,hcz,hc,hci,hFaces⟩ := L16Aux.smoothDomain_boundary_closed_flat_chart hO hzF
    exact fixed_data_locally_lipschitz_flat_chart hg hz e c hzS hcz hc hci
      (fun y hy => (hFaces y hy).2.1)

end Yau.LeafProofs.L16ExpBoundaryAux
