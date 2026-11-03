import Yau.Proofs.V02FlowSpray
import Yau.Proofs.V02SprayCenterTube

/-! One actual compact spray and one radius serve the original disc compact,
all prescribed centers, and every fixed chart in the finite cover. -/

open scoped Manifold Topology ContDiff Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02FlowProof

variable {n b q : ℕ} {X : KahlerManifold n}

theorem exists_realization_geometry
    {d : VariationData X q} (hd : VariationSetup d)
    (Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ)
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun u => (cotangentTransition (chartInv x u.1) x (cotangentChartInv x u) *ᵥ
        Z k (cotangentChartInv x u)) i) (cotangentTarget x))
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    {Kc : Set (CotangentCoord n × ℝ)} (hKc : IsCompact Kc)
    (hKcC : Kc ⊆ interior (centerCylinder d)) :
    ∃ (N : ℕ) (x : Fin N → X.manifold.Carrier) (a : Fin N → CotangentCoord n)
      (δ R : ℝ) (U : Set (NativeCotangentPoint X.manifold))
      (Kplus : Set (CotangentPoint X.manifold))
      (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) →
        NativeCotangentPoint X.manifold),
      0 < δ ∧ 0 < R ∧ IsOpen U ∧ (NativeCotangentPoint.mk '' K) ⊆ U ∧
      CotangentCompact Kplus ∧
      (∀ j, closedBall (a j) (8 * δ) ⊆ cotangentTarget (x j)) ∧
      (K ⊆ ⋃ j, cotangentChartInv (x j) '' ball (a j) δ) ∧
      (∀ y, Ψ (y, 0) = y) ∧
      ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
        𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R) ∧
      (∀ y, y.val ∈ K → ∀ τ ∈ closedBall (0 : Fin b → ℂ) (R / 2),
        (Ψ (y, τ)).val ∈ Kplus) ∧
      (∀ y ∈ U, ∀ k : Fin b,
        fderiv ℂ (fun τ : Fin b → ℂ => cotangentChart y.val.1 (Ψ (y, τ)).val)
          0 (Pi.single k 1) = cotangentVectorOfCoords (Z k y.val)) ∧
      (∀ j, ContDiffOn ℂ ∞ (nativeSprayCoordinate Ψ (x j))
        (ball (a j) (2 * δ) ×ˢ ball (0 : Fin b → ℂ) R)) ∧
      (∀ j u, u ∈ closedBall (a j) δ →
        ∀ τ ∈ closedBall (0 : Fin b → ℂ) (R / 2),
          (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x j) u), τ)).val ∈
            cotangentSource (x j)) ∧
      (∀ p ∈ Kc, NativeCotangentPoint.mk (cotangentChartInv d.chart p.1) ∈ U) ∧
      (∀ p ∈ Kc, ∀ τ ∈ closedBall (0 : Fin b → ℂ) R,
        InCotangentTimeChart d.chart
          (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1), τ)).val p.2
          (interior (centerCylinder d))) := by
  letI : T2Space (NativeCotangentPoint X.manifold) :=
    nativeCotangent_t2_of_immersion hd.2.2.2.2.1
  have hBig := realizationCompact_isCompact hd hK hKc hKcC
  obtain ⟨N, x, a, δ, R, U, Kplus, Ψ, hδ, hR, hU, hBU, hKplus,
    htarget, hcover, hUeq, hzero, hΨ, himage, hfirst, hcoord, _⟩ :=
    exists_native_compact_complex_spray Z hZ hBig
  have hinit : ∀ p ∈ Kc,
      NativeCotangentPoint.mk (cotangentChartInv d.chart p.1) ∈ U := by
    intro p hp
    exact hBU ⟨_, realizationCompact_center_mem d K hp, rfl⟩
  obtain ⟨Rc, hRc, hRcR, hcenter⟩ :=
    exists_uniform_spray_center_tube hd hKc hKcC hR hU hzero hΨ hinit
  obtain ⟨Rs, hRs, hRsR, hsource⟩ := exists_uniform_spray_chart_source hR hU hzero hΨ x a
    (fun j => (closedBall_subset_closedBall (by linarith : δ ≤ 8 * δ)).trans (htarget j))
    (fun j u hu => closed_chart_piece_mem_spray_union x a hδ hUeq j hu)
  let T := min R (min Rs Rc)
  have hT : 0 < T := lt_min hR (lt_min hRs hRc)
  have hTR : T ≤ R := min_le_left _ _
  have hTS : T ≤ Rs := (min_le_right R _).trans (min_le_left Rs Rc)
  have hTC : T ≤ Rc := (min_le_right R _).trans (min_le_right Rs Rc)
  refine ⟨N, x, a, δ, T, U, Kplus, Ψ, hδ, hT, hU, ?_, hKplus,
    htarget, ?_, hzero, ?_, ?_, hfirst, ?_, ?_, hinit, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hBU ⟨y, Or.inl hy, rfl⟩
  · exact fun y hy => hcover (Or.inl hy)
  · exact hΨ.mono (prod_mono (Subset.refl _) (ball_subset_ball hTR))
  · intro y hy τ hτ
    exact himage y (Or.inl hy) τ ((closedBall_subset_closedBall (by linarith)) hτ)
  · exact fun j => (hcoord j).mono (prod_mono (Subset.refl _) (ball_subset_ball hTR))
  · intro j u hu τ hτ
    exact hsource j u hu τ ((closedBall_subset_closedBall (by linarith)) hτ)
  · intro p hp τ hτ
    exact hcenter p hp τ ((closedBall_subset_closedBall hTC) hτ)

end Yau.Blueprint.V02Proof
