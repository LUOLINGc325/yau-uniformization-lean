import Yau.Proofs.V02CompactTube

/-! Uniform chart validity for the actual native spray follows from its
continuity and total zero-time identity on the compact initial chart pieces. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n b N : ℕ} {M : ComplexManifold n}

theorem exists_uniform_spray_chart_source
    {Ψ : NativeCotangentPoint M × (Fin b → ℂ) → NativeCotangentPoint M}
    {U : Set (NativeCotangentPoint M)} {R δ : ℝ} (hR : 0 < R) (hU : IsOpen U)
    (hzero : ∀ y, Ψ (y, 0) = y)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    (x : Fin N → M.Carrier) (a : Fin N → CotangentCoord n)
    (hTarget : ∀ j, closedBall (a j) δ ⊆ cotangentTarget (x j))
    (hInitial : ∀ j u, u ∈ closedBall (a j) δ →
      NativeCotangentPoint.mk (cotangentChartInv (x j) u) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ j u, u ∈ closedBall (a j) δ →
      ∀ τ ∈ closedBall (0 : Fin b → ℂ) (ρ / 2),
        (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x j) u), τ)).val ∈
          cotangentSource (x j) := by
  let F : Fin N → CotangentCoord n × (Fin b → ℂ) → NativeCotangentPoint M :=
    fun j p => Ψ (NativeCotangentPoint.mk (cotangentChartInv (x j) p.1), p.2)
  let O : Fin N → Set (NativeCotangentPoint M) :=
    fun j => (nativeCotangentChartHomeomorph (x j)).source
  have hO (j : Fin N) : IsOpen (O j) := (nativeCotangentChartHomeomorph (x j)).open_source
  have hFc (j : Fin N) (u : CotangentCoord n) (hu : u ∈ closedBall (a j) δ) :
      ContinuousAt (F j) (u, 0) := by
    let e := nativeCotangentChartHomeomorph (x j)
    have ht : u ∈ e.target := hTarget j hu
    have hInv : ContinuousAt
        (fun v => NativeCotangentPoint.mk (cotangentChartInv (x j) v)) u :=
      e.continuousOn_symm.continuousAt (e.open_target.mem_nhds ht)
    have hψ : ContinuousAt Ψ (NativeCotangentPoint.mk (cotangentChartInv (x j) u),
        (0 : Fin b → ℂ)) := (hΨ.contMDiffAt ((hU.prod isOpen_ball).mem_nhds
      (show (NativeCotangentPoint.mk (cotangentChartInv (x j) u), 0) ∈ U ×ˢ ball 0 R from
        ⟨hInitial j u hu, mem_ball_self hR⟩))).continuousAt
    have hI : ContinuousAt (fun p : CotangentCoord n × (Fin b → ℂ) =>
        (NativeCotangentPoint.mk (cotangentChartInv (x j) p.1), p.2)) (u, 0) :=
      (hInv.comp (continuous_fst.continuousAt : ContinuousAt
        (Prod.fst : CotangentCoord n × (Fin b → ℂ) → CotangentCoord n) (u, 0))).prodMk
          (continuous_snd.continuousAt : ContinuousAt
            (Prod.snd : CotangentCoord n × (Fin b → ℂ) → Fin b → ℂ) (u, 0))
    exact hψ.comp_of_eq hI rfl
  have hFzero (j : Fin N) (u : CotangentCoord n) (hu : u ∈ closedBall (a j) δ) :
      F j (u, 0) ∈ O j := by
    change Ψ (NativeCotangentPoint.mk (cotangentChartInv (x j) u), 0) ∈ O j
    rw [hzero]
    exact cotangentChartInv_mapsTo (x j) (hTarget j hu)
  obtain ⟨r, hr, hmap⟩ := finite_compact_parameter_tube
    (fun j : Fin N => isCompact_closedBall (a j) δ) hO hFc hFzero
  refine ⟨min R r, lt_min hR hr, min_le_left _ _, fun j u hu τ hτ => ?_⟩
  exact hmap j u hu τ ((closedBall_subset_closedBall
    ((half_le_self (lt_min hR hr).le).trans (min_le_right R r))) hτ)

end Yau.Blueprint.V02Proof
