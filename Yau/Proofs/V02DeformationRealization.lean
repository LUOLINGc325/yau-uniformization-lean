import Yau.Proofs.V02RealizationGeometry
import Yau.Proofs.V02NativeRealizes
import Yau.Proofs.V02CoefficientEuclidean
import Yau.Proofs.V02SprayTestUniform
import Yau.Proofs.V02WholeFunctional
import Yau.Proofs.V02AreaTaylor
import Yau.Proofs.V02WallTaylor

/-! Uniform actual native deformations retain the third jets of the same
whole functional, before the original scalar Taylor contract is extracted. -/

open scoped Manifold Topology ContDiff Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02FlowProof

variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_uniform_native_deformations
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (L E₀ D₀ ε η : ℝ) (hL : 0 ≤ L) (hη : 0 < η)
    (F : ℕ → VariationDisc X) (E : ℕ → ℂ → CotangentMatrix n)
    (l : ℕ → ℂ → CotangentIndex n → ℂ)
    (K : Set (CotangentPoint X.manifold)) (Kc : Set (CotangentCoord n × ℝ))
    (hK : CotangentCompact K) (hKc : IsCompact Kc)
    (hKcC : Kc ⊆ interior (centerCylinder d))
    (hdata : ∀ ν, AdmissibleVariationDisc d j (F ν) ∧
      (variationEnergy d j (F ν)).toReal ≤ E₀ ∧
      (∀ ζ ∈ closedBall (0 : ℂ) 1, (F ν).f ζ ∈ K) ∧
      InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc ∧
      NormalizedDiscFrame d.G (F ν).f (E ν) ∧ HolomorphicColumn (l ν) ∧
      (∀ ζ ∈ closedBall (0 : ℂ) 1, ∑ i, ‖l ν ζ i‖ ^ 2 ≤ L ^ 2) ∧
      boundaryDSq (fun θ => l ν (circlePoint θ)) ≤ ENNReal.ofReal (D₀ ^ 2)) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∃ (h α : ℕ → ℂ → ℂ) (fz : ℕ → ℂ → ℂ → CotangentPoint X.manifold),
        ∀ ν, RealizesFirstField d j a (F ν) (E ν) (l ν) (h ν) (α ν) (fz ν) r ∧
          (α ν 0).im = 0 ∧ 0 < (α ν 0).re ∧ -Real.log (α ν 0).re ≤ η ∧
          circleAverage (fun θ => 1 - ‖α ν (circlePoint θ)‖ ^ 2) ≤ η ∧
          ContDiffOn ℝ 3 (fun z => penalizedFunctional d j ε {(F ν) with f := fz ν z})
            (ball (0 : ℂ) r) ∧
          ∀ z ∈ ball (0 : ℂ) r,
            ‖iteratedFDeriv ℝ 3
              (fun w => penalizedFunctional d j ε {(F ν) with f := fz ν w}) z‖ ≤ M := by
  obtain ⟨b, Z, hZ, hspan⟩ := hd.2.2.2.2.2.1
  obtain ⟨N, x, A, δ, R, U, Kplus, Ψ, hδ, hR, hU, hKU, _, htarget, hcover,
    hzero, hΨ, _, hfirst, hcoord, hsource, hInitial, hTube⟩ :=
    exists_realization_geometry hd Z hZ hK hKc hKcC
  obtain ⟨P, C, S, hP, hC, hS, hcoeff⟩ :=
    exists_uniform_spanningFirstCoefficients hd j hZ hspan hK L hL E₀ D₀ hη
  let C₀ := ((b : ℝ) + 1) * C
  let D₁ := (b : ℝ) * S
  let H₀ := 4 * (a : ℝ) ^ 2 * max E₀ 0
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by positivity) hC
  have hD₁ : 0 ≤ D₁ := mul_nonneg (Nat.cast_nonneg b) hS
  have hH₀ : 0 ≤ H₀ := by dsimp [H₀]; positivity
  have hCC : C ≤ C₀ := by
    dsimp [C₀]
    nlinarith [mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hC]
  have hKUn : ∀ y ∈ K, NativeCotangentPoint.mk y ∈ U :=
    fun y hy => hKU ⟨y, hy, rfl⟩
  obtain ⟨ra, hra, _, MA, hMA, hArea⟩ :=
    V02AreaTaylorProof.exists_uniform_spray_spatialArea_C3 hd.2.2.2.2.1 x A hδ hR
      (fun k => (closedBall_subset_closedBall (by linarith : δ ≤ 8 * δ)).trans (htarget k))
      hcover hKUn hΨ (fun k => hcoord k) hsource
      (E0 := max E₀ 0) (H0 := H₀) (C0 := C₀) (D0 := D₁)
      (le_max_right _ _) hH₀ hC₀ hD₁
  obtain ⟨rb, MB, ML, hrw, hrwR, hMB, hML, hWall⟩ :=
    V02WallTaylorProof.exists_uniform_spray_boundary_log_C3 hd j a ha hU K hK hKUn x A
      hδ hR htarget hcover hzero hΨ (fun k => hcoord k) hsource
      (E0 := max E₀ 0) (C0 := C₀) (D0 := D₁) (le_max_right _ _) hC₀ hD₁
  obtain ⟨rt, MT, hrt, _, hMT, hTest⟩ :=
    exists_uniform_spray_test_C3 hd hKc hKcC hR hC₀ hU hΨ hInitial hTube
  let r := min ra (min rb rt)
  have hr : 0 < r := lt_min hra (lt_min hrw hrt)
  have hra' : r ≤ ra := min_le_left _ _
  have hrw' : r ≤ rb := (min_le_right ra _).trans (min_le_left rb rt)
  have hrt' : r ≤ rt := (min_le_right ra _).trans (min_le_right rb rt)
  have hrR : r ≤ R / (2 * (C₀ + 1)) := hrw'.trans hrwR.le
  let M := MB + |ε| * (MA + ML) + MT
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let h : ℕ → ℂ → ℂ := fun ν => outerCandidate (logTrace d j (F ν).f) a
  let α : ℕ → ℂ → ℂ := fun ν => spanningDamping P d.G Z (F ν).f
  let c : ℕ → ℂ → Fin b → ℂ :=
    fun ν => spanningFirstCoefficients d.G Z (F ν).f (E ν) (l ν) (α ν)
  let fz : ℕ → ℂ → ℂ → CotangentPoint X.manifold :=
    fun ν => nativeSprayFamily Ψ (F ν).f (h ν) (c ν)
  refine ⟨r, M, hr, hM, h, α, fz, fun ν => ?_⟩
  obtain ⟨hF, hE, hFK, hcenter, hframe, hl, hsup, hD⟩ := hdata ν
  obtain ⟨hα, hphase, hpos, hαsup, hαD, hlog, hloss, hc⟩ :=
    hcoeff (F ν) (E ν) (l ν) hF hE hFK hframe hl hsup hD
  have hcSmooth (k : Fin b) : ContDiffOn ℂ ∞ (fun ζ => c ν ζ k) (closedBall 0 1) := (hc k).1
  have hcC : ∀ ζ ∈ closedBall (0 : ℂ) 1, ∀ k, ‖c ν ζ k‖ ≤ C :=
    fun ζ hζ k => (hc k).2.1 ζ hζ
  have hcC₀ : ∀ ζ ∈ closedBall (0 : ℂ) 1, ∀ k, ‖c ν ζ k‖ ≤ C₀ :=
    fun ζ hζ k => (hcC ζ hζ k).trans hCC
  have hcPi : ∀ ζ ∈ closedBall (0 : ℂ) 1, ‖c ν ζ‖ ≤ C₀ :=
    fun ζ hζ => (pi_norm_le_iff_of_nonneg hC₀).mpr (hcC₀ ζ hζ)
  have hcEu := coefficientsEuclidean_contDiffOn hcSmooth
  have hcEuNorm := coefficientsEuclidean_norm_bound hC hcC
  have hcD := coefficientsEuclidean_boundary_budget (c := c ν) (S := S) (fun k => (hc k).2.2)
  have hcD' : boundaryDSq (fun θ k => c ν (circlePoint θ) k) ≤ ENNReal.ofReal D₁ := hcD
  obtain ⟨hh, _, _, _, hhsup⟩ := original_outer_properties hd hF a
  have hH := original_outer_boundary_budget hd j a E₀ (F ν) hF hE
  obtain ⟨hboundary, hbc, hlogC⟩ := hWall (F ν) hF (hE.trans (le_max_left _ _)) hFK
    (c ν) hcSmooth hcPi hcD'
  have hReal : RealizesFirstField d j a (F ν) (E ν) (l ν) (h ν) (α ν) (fz ν) r :=
    realizesFirstField_of_native_spray hd j a hU hR hr hC₀ hrR hzero hΨ hZ hspan hfirst
      hTube (F ν) (E ν) (l ν) (α ν) hF hcenter
      (fun ζ hζ => hKUn _ (hFK ζ hζ)) hframe hl hα hαsup hαD hcC₀
      (fun z hz θ => hboundary z ((ball_subset_ball hrw') hz) θ)
  have hAE : (euclideanArea (fun ζ => d.G ((F ν).f ζ))).toReal ≤ max E₀ 0 :=
    ((ENNReal.toReal_mono hF.2.2.2.2.2.2.2.2 (euclideanArea_le_variationEnergy d j (F ν))).trans hE).trans
      (le_max_left _ _)
  have harea := hArea (F ν).f hF.1 hFK (h ν) hh hhsup
    (coefficientsEuclidean (c ν)) hcEu hcEuNorm hAE hH hcD
  have ht := hTest (F ν) (h ν) (c ν) hcenter (hhsup 0 (by simp)) (hcPi 0 (by simp))
  have hwhole := penalizedFunctional_C3_of_actual_parts hd.2.2.2.2.1 j (F ν) (fz ν) ε
    hReal.2.1 (harea.1.mono (ball_subset_ball hra')) (hbc.1.mono (ball_subset_ball hrw'))
    (hlogC.1.mono (ball_subset_ball hrw')) (ht.1.mono (ball_subset_ball hrt'))
    (fun z hz => harea.2 z ((ball_subset_ball hra') hz))
    (fun z hz => hbc.2 z ((ball_subset_ball hrw') hz))
    (fun z hz => hlogC.2 z ((ball_subset_ball hrw') hz))
    (fun z hz => ht.2 z ((ball_subset_ball hrt') hz))
  exact ⟨hReal, hphase, hpos, hlog, hloss, hwhole.1, hwhole.2⟩

theorem deformationRealization {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) : DeformationRealization d j a := by
  intro L E₀ D₀ ε η hL _ hη F E l K Kc hK hKc hKcC hdata
  obtain ⟨r, M, hr, hM, h, α, fz, hall⟩ :=
    exists_uniform_native_deformations hd j a ha L E₀ D₀ ε η hL hη F E l K Kc hK hKc hKcC hdata
  refine ⟨r, M / 2, hr, div_nonneg hM (by norm_num), h, α, fz,
    fun ν => ⟨(hall ν).1, (hall ν).2.1, (hall ν).2.2.1, (hall ν).2.2.2.1,
      (hall ν).2.2.2.2.1⟩, fun ν ρ hρ hρr => ?_⟩
  exact parameterCircleTaylor (hall ν).2.2.2.2.2.1 (hall ν).2.2.2.2.2.2 hρ hρr

end Yau.Blueprint.V02Proof
