import Yau.LeafProofs.L16ExpBoundaryCombinedBarrier
import Yau.LeafProofs.L16ExpBoundaryLocalDomain

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- One defining-function chart gives one linear boundary modulus, uniformly
for every coefficient field and solution satisfying the fixed bounds. The
artificial sphere is handled by the actual squared-distance correction. -/
theorem local_boundary_modulus_of_defining_data {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcompact : IsCompact (closure O))
    {T ν upper A₀ b₀ H W₀ : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀) (hH : 0 < H) (hW₀ : 0 < W₀)
    {x : Space n} {s : Space n → ℝ} {R a₀ M₁ M₂ S₀ : ℝ}
    (hR : 0 < R) (ha₀ : 0 < a₀) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hs : ∀ z ∈ Metric.ball x R, ContDiffAt ℝ 2 s z)
    (hjets : ∀ z ∈ Metric.ball x R, a₀ ≤ ‖fderiv ℝ s z‖ ∧
      ‖fderiv ℝ s z‖ ≤ M₁ ∧ ‖fderiv ℝ (fderiv ℝ s) z‖ ≤ M₂ ∧ |s z| ≤ S₀)
    (hnonneg : ∀ z ∈ closure O ∩ Metric.ball x R, 0 ≤ s z)
    (hzero : ∀ z ∈ frontier O ∩ Metric.ball x R, s z = 0) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ),
        Elliptic (O ×ˢ Ioo 0 T) a ν upper →
        (∀ z ∈ O ×ˢ Ioo 0 T, ∀ i j, |a z i j| ≤ A₀) →
        (∀ z ∈ O ×ˢ Ioo 0 T, ∀ i, |b z i| ≤ b₀) →
        ContinuousOn u (cylinder (closure O) 0 T) →
        (∀ z ∈ O ×ˢ Ioo 0 T, ContDiffAt ℝ 2 (fun y => u (y,z.2)) z.1) →
        (∀ z ∈ O ×ˢ Ioo 0 T, DifferentiableAt ℝ (fun t => u (z.1,t)) z.2) →
        (∀ z ∈ closure O, u (z,0) = 0) →
        (∀ z ∈ frontier O, ∀ t ∈ Icc 0 T, u (z,t) = 0) →
        (∀ z ∈ cylinder (closure O) 0 T, |u z| ≤ W₀) →
        (∀ z ∈ O ×ˢ Ioo 0 T, |linearOp (cylinder (closure O) 0 T) a b u z| ≤ H) →
        ∀ y ∈ frontier O ∩ Metric.ball x (R/4),
          ∀ z ∈ closure O ∩ Metric.ball y (R/4), ∀ t ∈ Icc 0 T,
            |u (z,t)| ≤ K*‖z-y‖ := by
  classical
  let r : ℝ := R/4
  have hr : 0 < r := by dsimp [r]; positivity
  let Lρ : ℝ := (∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, A₀*M₂) +
    ∑ _i : Yau.RIdx n, b₀*M₁
  have hLρ : 0 ≤ Lρ := by dsimp [Lρ]; positivity
  obtain ⟨κ,μ,hκ,hμ,hgap,hμeq⟩ := exists_definingBarrier_constants (S₀ := S₀) hν ha₀ hLρ
  let c : ℝ := W₀/r^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let C : ℝ := (∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, A₀*2) +
    ∑ _i : Yau.RIdx n, b₀*(2*r)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let K₀ : ℝ := (H+c*C+1)/μ
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hConst : H+c*C ≤ K₀*μ := by
    have heq : K₀*μ = H+c*C+1 := by dsimp [K₀]; field_simp
    linarith
  refine ⟨1+K₀*κ*M₁+W₀/r,by positivity,?_⟩
  intro a b u he hA hb hu hsU htU hi hl hsup hop y hy z hz t ht
  let D : Set (Space n) := O ∩ Metric.ball y r
  let W : Space n → ℝ := combinedBarrier s κ K₀ c y
  have hD : IsOpen D := hO.inter Metric.isOpen_ball
  have hcl : closure D ⊆ closure O ∩ Metric.closedBall y r := closure_inter_ball_subset O y r
  have hclO : closure D ⊆ closure O := fun p hp => (hcl hp).1
  have hclChart : closure D ⊆ Metric.ball x R := by
    intro p hp
    exact nearby_closedBall_in_chart hR hy.2 (hcl hp).2
  have hDcompact : IsCompact (closure D) := hcompact.of_isClosed_subset isClosed_closure hclO
  have hDU : D ×ˢ Ioo 0 T ⊆ O ×ˢ Ioo 0 T := fun p hp => ⟨hp.1.1,hp.2⟩
  have hDQ : cylinder (closure D) 0 T ⊆ cylinder (closure O) 0 T :=
    fun p hp => ⟨hclO hp.1,hp.2⟩
  have hWc : ContinuousOn W (closure D) := by
    intro p hp
    exact (combinedBarrier_contDiffAt (hs p (hclChart hp))).continuousAt.continuousWithinAt
  have hWs : ∀ p ∈ D, ContDiffAt ℝ 2 W p :=
    fun p hp => combinedBarrier_contDiffAt (hs p (hclChart (subset_closure hp)))
  have hWnonneg : ∀ p ∈ closure D, 0 ≤ W p := by
    intro p hp
    exact combinedBarrier_nonneg hκ.le hK₀.le hc (hnonneg p ⟨hclO hp,hclChart hp⟩)
  have hbar : ∀ p ∈ D ×ˢ Ioo 0 T, H ≤ stationaryOp (a p) (b p) W p.1 := by
    intro p hp
    have hpChart := hclChart (subset_closure hp.1)
    have hj := hjets p.1 hpChart
    have hLp : |(∑ i, ∑ j, a p i j*fderiv ℝ (fderiv ℝ s) p.1 (Yau.realVec i) (Yau.realVec j)) +
        ∑ i, b p i*d s p.1 i| ≤ Lρ :=
      definingFunction_contraction_abs_bound hA₀ hb₀ hj.2.1 hj.2.2.1 (hA p (hDU hp)) (hb p (hDU hp))
    have hJ : μ ≤ stationaryOp (a p) (b p) (definingBarrier s κ) p.1 := by
      rw [hμeq]
      exact definingBarrier_operator_lower_bound (hs p.1 hpChart) hκ hν ha₀ hgap hj.1
        ((le_abs_self _).trans hj.2.2.2) (fun v => ((he.2.2 p (hDU hp)).2 v).1) hLp
    have hSphere : |stationaryOp (a p) (b p) (sphereBarrier y) p.1| ≤ C :=
      sphereBarrier_operator_abs_bound hA₀ hb₀ (hA p (hDU hp)) (hb p (hDU hp))
        (by exact (show ‖p.1-y‖ < r by simpa only [Metric.mem_ball,dist_eq_norm] using hp.1.2).le)
    exact combinedBarrier_operator_lower_bound (hs p.1 hpChart) hK₀.le hc hJ hSphere hConst
  have hbound := stationary_barrier_abs (O := D) (b := b) hD hDcompact hT
    (hu.mono hDQ) (fun p hp => hsU p (hDU hp)) (fun p hp => htU p (hDU hp))
    ⟨he.1,he.2.1,fun p hp => he.2.2 p (hDU hp)⟩ hWc hWs
    (by intro p hp; rw [hi p (hclO hp),abs_zero]; exact hWnonneg p hp)
    (by
      intro p hp v hv
      rcases frontier_inter_ball_cases hO hp with hpO | hpSphere
      · rw [hl p hpO v hv,abs_zero]
        exact hWnonneg p hp.1
      · exact (hsup (p,v) ⟨hpSphere.1,hv⟩).trans
          (combinedBarrier_on_sphere hκ.le hK₀.le hr
            (hnonneg p ⟨hclO hp.1,hclChart hp.1⟩) hpSphere.2))
    (by
      intro p hp
      rw [linearOp_closed_domain_eq (hclO (subset_closure hp.1)) (subset_closure hp.1)]
      exact hop p (hDU hp)) hbar
  have hzD : z ∈ closure D := Metric.isOpen_ball.closure_inter ⟨hz.1,hz.2⟩
  have hyChart : y ∈ Metric.ball x R := Metric.ball_subset_ball (by linarith) hy.2
  have hsy : s y = 0 := hzero y ⟨hy.1,hyChart⟩
  have hsz : s z ≤ M₁*‖z-y‖ := definingFunction_nearby_linear_bound hR hy.2
    (Metric.ball_subset_closedBall hz.2) (fun p hp => (hs p hp).differentiableAt (by norm_num))
    (fun p hp => (hjets p hp).2.1) hsy
  have hzdist : ‖z-y‖ ≤ r :=
    (show ‖z-y‖ < r by simpa only [Metric.mem_ball,dist_eq_norm] using hz.2).le
  have hWlinear := combinedBarrier_le_linear hκ.le hK₀.le hW₀.le hr hsz hzdist
  exact (hbound (z,t) ⟨hzD,ht⟩).trans (hWlinear.trans (by nlinarith [norm_nonneg (z-y)]))

end Yau.LeafProofs.L16ExpBoundaryAux
