import Yau.Proofs.V02RealizationCompact

/-! The actual native spray preserves the original open center cylinder on
a common parameter tube over every prescribed compact set of centers. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n b q : ℕ} {X : KahlerManifold n}

theorem exists_uniform_spray_center_tube
    {d : VariationData X q} (hd : VariationSetup d)
    {Kc : Set (CotangentCoord n × ℝ)} (hKc : IsCompact Kc)
    (hKcC : Kc ⊆ interior (centerCylinder d))
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) →
      NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {R : ℝ}
    (hR : 0 < R) (hU : IsOpen U) (hzero : ∀ y, Ψ (y, 0) = y)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    (hInitial : ∀ p ∈ Kc,
      NativeCotangentPoint.mk (cotangentChartInv d.chart p.1) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ p ∈ Kc,
      ∀ τ ∈ closedBall (0 : Fin b → ℂ) ρ,
        InCotangentTimeChart d.chart
          (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1), τ)).val p.2
          (interior (centerCylinder d)) := by
  let e := (nativeCotangentChartHomeomorph d.chart).prod
    (OpenPartialHomeomorph.refl ℝ)
  let O := e.source ∩ e ⁻¹' interior (centerCylinder d)
  let F : (CotangentCoord n × ℝ) × (Fin b → ℂ) →
      NativeCotangentPoint X.manifold × ℝ :=
    fun p => (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1.1), p.2), p.1.2)
  have hO : IsOpen O := e.isOpen_inter_preimage isOpen_interior
  have ht (p) (hp : p ∈ Kc) : p.1 ∈ cotangentTarget d.chart :=
    (hd.2.2.2.2.2.2.2.1.2.2.1 (interior_subset (hKcC hp))).1
  have hFc (p) (hp : p ∈ Kc) : ContinuousAt F (p, 0) := by
    have hInv : ContinuousAt
        (fun u => NativeCotangentPoint.mk (cotangentChartInv d.chart u)) p.1 :=
      (nativeCotangentChartHomeomorph d.chart).continuousOn_symm.continuousAt
        ((nativeCotangentChartHomeomorph d.chart).open_target.mem_nhds (ht p hp))
    have hψ : ContinuousAt Ψ
        (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1), (0 : Fin b → ℂ)) :=
      (hΨ.contMDiffAt ((hU.prod isOpen_ball).mem_nhds
        ⟨hInitial p hp, mem_ball_self hR⟩)).continuousAt
    have hfst : ContinuousAt
        (fun v : (CotangentCoord n × ℝ) × (Fin b → ℂ) => v.1.1) (p, 0) :=
      continuous_fst.fst.continuousAt
    have hI : ContinuousAt
        (fun v : (CotangentCoord n × ℝ) × (Fin b → ℂ) =>
          (NativeCotangentPoint.mk (cotangentChartInv d.chart v.1.1), v.2)) (p, 0) :=
      (hInv.comp_of_eq hfst rfl).prodMk continuous_snd.continuousAt
    exact (hψ.comp_of_eq hI rfl).prodMk continuous_fst.snd.continuousAt
  have hFzero (p) (hp : p ∈ Kc) : F (p, 0) ∈ O := by
    change (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1), 0), p.2) ∈ O
    rw [hzero]
    constructor
    · exact ⟨cotangentChartInv_mapsTo d.chart (ht p hp), mem_univ _⟩
    · change (cotangentChart d.chart (cotangentChartInv d.chart p.1), p.2) ∈
        interior (centerCylinder d)
      rw [cotangentChart_right_inv d.chart (ht p hp)]
      exact hKcC hp
  obtain ⟨r, hr, hmap⟩ := compact_parameter_tube hKc hO hFc hFzero
  refine ⟨min R r, lt_min hR hr, min_le_left _ _, fun p hp τ hτ => ?_⟩
  have hm := hmap p hp τ ((closedBall_subset_closedBall (min_le_right R r)) hτ)
  exact ⟨hm.1.1, hm.2⟩

end Yau.Blueprint.V02Proof
