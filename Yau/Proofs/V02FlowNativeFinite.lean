import Yau.Proofs.V02FlowGlue
import Yau.Proofs.V02FlowFiniteBudgets

/-! A finite family of genuine native holomorphic fields has one common local flow radius. -/

open scoped Manifold Topology ContDiff Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n N b : ℕ} {M : ComplexManifold n} [T2Space (NativeCotangentPoint M)]

theorem exists_native_finite_chart_flows
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (x : Fin N → M.Carrier) (a : Fin N → CotangentCoord n) {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ j, closedBall (a j) (8 * δ) ⊆ cotangentTarget (x j)) :
    ∃ (R A : ℝ) (φ : Fin N × Fin b → ℂ × CotangentCoord n → CotangentCoord n)
      (Φ : Fin b → ℂ × NativeCotangentPoint M → NativeCotangentPoint M),
      0 < R ∧ 0 ≤ A ∧ R * A ≤ δ / 4 ∧
      (∀ i, (∀ u, φ i (0, u) = u) ∧
        ContDiffOn ℂ ∞ (φ i) (ball (0 : ℂ) R ×ˢ ball (a i.1) (4 * δ)) ∧
        (∀ p ∈ closedBall (0 : ℂ) R ×ˢ closedBall (a i.1) (4 * δ),
          ‖φ i p - p.2‖ ≤ ‖p.1‖ * A) ∧
        (∀ t ∈ ball (0 : ℂ) R, ∀ u ∈ ball (a i.1) (4 * δ),
          φ i (t, u) ∈ ball (a i.1) (8 * δ) ∧
          HasDerivAt (fun z : ℂ => φ i (z, u))
            (cotangentChartField (Z i.2) (x i.1) (φ i (t, u))) t)) ∧
      (∀ k, (∀ y, Φ k (0, y) = y) ∧
        ContMDiffOn ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentCoord n))
          𝓘(ℂ, CotangentCoord n) ∞ (Φ k)
          (ball (0 : ℂ) R ×ˢ ⋃ j, nativeCotangentChartBall (x j) (a j) (4 * δ)) ∧
        ∀ j t, t ∈ ball (0 : ℂ) R → ∀ y,
          y ∈ nativeCotangentChartBall (x j) (a j) (4 * δ) →
          Φ k (t, y) = nativeChartFlow (x j) (φ (j, k)) (t, y)) := by
  let Ω : Fin N × Fin b → Set (CotangentCoord n) := fun i => cotangentTarget (x i.1)
  let W : Fin N × Fin b → CotangentCoord n → CotangentCoord n :=
    fun i => cotangentChartField (Z i.2) (x i.1)
  obtain ⟨R, A, φ, hR, hA, hRA, hφ⟩ := exists_finite_uniform_holomorphic_flows
    Ω W (fun i => a i.1) hδ
    (fun i => (isOpen_extChartAt_target (I := ComplexModel n) (x i.1)).prod isOpen_univ)
    (fun i => cotangentChartField_differentiableOn (hZ i.2) (x i.1))
    (fun i => hball i.1)
  let U : Fin N → Set (NativeCotangentPoint M) :=
    fun j => nativeCotangentChartBall (x j) (a j) (4 * δ)
  let F : Fin b → Fin N → ℂ × NativeCotangentPoint M → NativeCotangentPoint M :=
    fun k j => nativeChartFlow (x j) (φ (j, k))
  have hball4 : ∀ j, ball (a j) (4 * δ) ⊆ cotangentTarget (x j) := fun j =>
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans (hball j)
  have hU : ∀ j, IsOpen (U j) := fun j => nativeCotangentChartBall_isOpen (hball4 j)
  have hφzero : ∀ i u, φ i (0, u) = u := fun i => (hφ i).1
  have hφimage : ∀ i p, p ∈ ball (0 : ℂ) R ×ˢ ball (a i.1) (4 * δ) →
      φ i p ∈ cotangentTarget (x i.1) := by
    intro i p hp
    exact hball i.1 (ball_subset_closedBall ((hφ i).2.2.2.2 p.1 hp.1 p.2 hp.2).1)
  have hFzero : ∀ k j y, y ∈ U j → F k j (0, y) = y := by
    intro k j y hy
    exact nativeChartFlow_zero (x j) (hφzero (j, k))
      (((nativeCotangentChartBall_mem_iff (hball4 j)).mp hy).1)
  have hFcurve : ∀ k j y, y ∈ U j →
      NativeFieldIntegralCurve (Z k) (fun t => F k j (t, y)) (ball (0 : ℂ) R) := by
    intro k j y hy
    have hcoords := ((nativeCotangentChartBall_mem_iff (hball4 j)).mp hy).2
    exact nativeChartFlow_integralCurve (x j) isOpen_ball y
      (fun t ht => hφimage (j, k) _ ⟨ht, hcoords⟩)
      (fun t ht => ((hφ (j, k)).2.2.2.2 t ht _ hcoords).2)
  have hcompat : ∀ k i j t, t ∈ ball (0 : ℂ) R → ∀ y, y ∈ U i → y ∈ U j →
      F k i (t, y) = F k j (t, y) := by
    intro k i j t ht y hyi hyj
    exact native_complex_ode_unique_on_ball (hZ k) (hFcurve k i y hyi) (hFcurve k j y hyj)
      ((hFzero k i y hyi).trans (hFzero k j y hyj).symm) ht
  let Φ : Fin b → ℂ × NativeCotangentPoint M → NativeCotangentPoint M :=
    fun k => nativeFlowGlue U (F k) R
  refine ⟨R, A, φ, Φ, hR, hA, hRA, ?_, ?_⟩
  · intro i
    exact ⟨(hφ i).1, (hφ i).2.1, (hφ i).2.2.2.1, (hφ i).2.2.2.2⟩
  · intro k
    refine ⟨nativeFlowGlue_zero (hFzero k), ?_, ?_⟩
    · exact nativeFlowGlue_contMDiffOn hU
        (fun j => nativeChartFlow_contMDiffOn (x j) (hball4 j) (hφ (j, k)).2.1
          (hφimage (j, k))) (hcompat k)
    · exact fun j t ht y hy => nativeFlowGlue_eq_branch (hcompat k) j ht hy

end Yau.Blueprint.V02FlowProof
