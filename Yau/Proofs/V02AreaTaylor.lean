import Yau.Proofs.V02AreaTaylorPointwise

/-! Uniform actual third parameter derivatives of the original sum of
base, immersion and Gauss areas, before choosing any input disc or coefficients. -/

open scoped Topology ContDiff Matrix Manifold
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

set_option synthInstance.maxHeartbeats 100000

variable {n q b N : ℕ} {X : KahlerManifold n}

theorem exists_uniform_spray_spatialArea_C3 {d : VariationData X q}
    (hG : CotangentImmersion d.G)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {K : Set (CotangentPoint X.manifold)}
    (x : Fin N → Pt X) (a : Fin N → CotangentCoord n) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R)
    (htarget : ∀ j, Metric.closedBall (a j) δ ⊆ cotangentTarget (x j))
    (hcover : K ⊆ ⋃ j, cotangentChartInv (x j) '' Metric.ball (a j) δ)
    (hKU : ∀ y ∈ K, NativeCotangentPoint.mk y ∈ U)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ Metric.ball 0 R))
    (hψ : ∀ j, ContDiffOn ℂ ∞ (sprayCoordinate Ψ (x j))
      (Metric.ball (a j) (2 * δ) ×ˢ Metric.ball 0 R))
    (hsource : ∀ j, ∀ u ∈ Metric.closedBall (a j) δ,
      ∀ τ ∈ Metric.closedBall (0 : Fin b → ℂ) (R / 2),
        (Ψ (NativeCotangentPoint.mk (cotangentChartInv (x j) u), τ)).val ∈ cotangentSource (x j))
    {E0 H0 C0 D0 : ℝ} (hE0 : 0 ≤ E0) (hH0 : 0 ≤ H0) (hC0 : 0 ≤ C0) (hD0 : 0 ≤ D0) :
    ∃ r : ℝ, 0 < r ∧ r < R / (2 * (C0 + 1)) ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ (f : ℂ → CotangentPoint X.manifold), CotangentDisc f →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, f ζ ∈ K) →
      ∀ (h : ℂ → ℂ), ContDiffOn ℂ ∞ h (Metric.closedBall 0 1) →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖h ζ‖ ≤ 1) →
      ∀ (c : ℂ → ComplexVector b), ContDiffOn ℂ ∞ c (Metric.closedBall 0 1) →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖c ζ‖ ≤ C0) →
      (euclideanArea (fun ζ => d.G (f ζ))).toReal ≤ E0 →
      boundaryDSq (fun θ (_ : Unit) => h (circlePoint θ)) ≤ ENNReal.ofReal H0 →
      boundaryDSq (fun θ k => c (circlePoint θ) k) ≤ ENNReal.ofReal D0 →
      ContDiffOn ℝ 3 (fun z => spatialArea d (sprayFamily Ψ f h c z)) (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r,
        ‖iteratedFDeriv ℝ 3 (fun p => spatialArea d (sprayFamily Ψ f h c p)) z‖ ≤ M := by
  classical
  choose C hC hCb using fun j => chart_spatialDensity_uniform_jet_bound hG (x j) (a j)
    hδ hR hC0 (htarget j) (hψ j) (hsource j) 3
  let S : ℝ := ∑ j, C j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hC j
  let M : ℝ := S * (E0 / 2 + Real.pi * H0 + Real.pi * D0)
  have hM : 0 ≤ M := mul_nonneg hS (by positivity)
  refine ⟨sprayRadius R C0, sprayRadius_pos hR hC0, sprayRadius_lt hR hC0, M, hM, ?_⟩
  intro f hf hfK h hh hh0 c hc hc0 hE hH hD
  have hfamily : CotangentHolomorphicOn (fun p : ℂ × ℂ => sprayFamily Ψ f h c p.1 p.2)
      (Metric.ball (0 : ℂ) (2 * sprayRadius R C0) ×ˢ Metric.closedBall (0 : ℂ) 1) := by
    apply sprayFamily_holomorphic hΨ hf (fun ζ hζ => hKU _ (hfK ζ hζ)) hh hc
    intro p hp
    have htime := sprayTimes_mem_half hR hC0
      (le_of_lt (by simpa using Metric.mem_ball.mp hp.1)) (hh0 _ hp.2) (hc0 _ hp.2)
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp htime).trans_lt (by linarith))
  have hslice : ∀ z ∈ Metric.ball (0 : ℂ) (2 * sprayRadius R C0),
      CotangentDisc (sprayFamily Ψ f h c z) := fun z hz =>
    (hfamily.comp (contDiff_const.prodMk contDiff_id) (fun _ hζ => ⟨hz, hζ⟩)).cotangentDisc
  have hsmooth := spatialArea_family_contDiffOn hG Metric.isOpen_ball hfamily
  have hdensity := spatialDensity_joint_contDiffOn hG Metric.isOpen_ball hfamily
  have hweight := inputDerivativeWeight_integrable (cotangentDisc_ambient_contDiffOn hf hG.1) hh hc
  have hweight0 : ∀ ζ : ℂ, 0 ≤ inputDerivativeWeight (fun η => d.G (f η)) h c ζ :=
    fun ζ => by unfold inputDerivativeWeight; positivity
  have hbudget := integral_inputDerivativeWeight_le (cotangentDisc_ambient_contDiffOn hf hG.1)
    hh hc hH0 hD0 hE hH hD
  have hr := sprayRadius_pos hR hC0
  refine ⟨(hsmooth.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith)), ?_⟩
  intro z hz
  have hz2 : z ∈ Metric.ball (0 : ℂ) (2 * sprayRadius R C0) :=
    Metric.ball_subset_ball (by linarith) hz
  have heq : (fun p => spatialArea d (sprayFamily Ψ f h c p)) =ᶠ[𝓝 z]
      (fun p => ∫ ζ in Metric.ball (0 : ℂ) 1, spatialDensity d (sprayFamily Ψ f h c p) ζ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz2] with p hp
    exact spatialArea_eq_integral_spatialDensity hG (hslice p hp)
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) 3).eq_of_nhds]
  have hnorm := norm_iteratedFDeriv_discIntegral_le Metric.isOpen_ball hdensity hz2 3
    (hweight.const_mul S) (fun ζ _ => mul_nonneg hS (hweight0 ζ))
    (w := fun ζ => S * inputDerivativeWeight (fun η => d.G (f η)) h c ζ) (by
      intro ζ hζ
      have hζc := Metric.ball_subset_closedBall hζ
      obtain ⟨j, u, hu, he⟩ := Set.mem_iUnion.mp (hcover (hfK ζ hζc))
      have hut := htarget j (Metric.ball_subset_closedBall hu)
      have hx : f ζ ∈ cotangentSource (x j) := by
        rw [← he]
        exact cotangentChartInv_mapsTo (x j) hut
      have hcoord : cotangentChart (x j) (f ζ) ∈ Metric.closedBall (a j) δ := by
        rw [← he, cotangentChart_right_inv (x j) hut]
        exact Metric.ball_subset_closedBall hu
      have hb := hCb j f hf h hh c hc hslice ζ hζc hx hcoord (hh0 ζ hζc) (hc0 ζ hζc)
        z (Metric.ball_subset_closedBall hz)
      exact hb.trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)) (hweight0 ζ)))
  calc
    _ ≤ ∫ ζ in Metric.ball (0 : ℂ) 1, S * inputDerivativeWeight (fun η => d.G (f η)) h c ζ := hnorm
    _ = S * (∫ ζ in Metric.ball (0 : ℂ) 1, inputDerivativeWeight (fun η => d.G (f η)) h c ζ) := integral_const_mul _ _
    _ ≤ M := mul_le_mul_of_nonneg_left hbudget hS

end Yau.Blueprint.V02AreaTaylorProof
