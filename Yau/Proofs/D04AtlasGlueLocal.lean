import Yau.Proofs.D04AtlasGluePotential
import Yau.Proofs.D04AtlasGlueError
import Yau.Proofs.D04AtlasGlueCoordinate

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem isPshOn_congr {D : Set (ComplexVector n)} {u v : ComplexVector n → EReal}
    (hu : IsPshOn u D) (heq : EqOn v u D) : IsPshOn v D := by
  refine ⟨fun z hz => heq hz ▸ hu.1 z hz, ?_, ?_⟩
  · intro z hz
    exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq
      (hu.2.1 z hz) hz heq.symm.eventuallyEq_nhdsWithin
  · intro z w hdisc f hf hmajor
    have hz : z ∈ D := by simpa using hdisc 0 (by simp)
    rw [heq hz]
    apply hu.2.2 z w hdisc f hf
    intro θ
    rw [← heq (hdisc (Complex.exp (θ * Complex.I)) (by simp))]
    exact hmajor θ

theorem chart_compact_coordinates (a : M.Carrier)
    {D : Set (ComplexVector n)} (hDt : D ⊆ chartTarget a)
    {K : Set M.Carrier} (hK : IsCompact K) (hKW : K ⊆ chartInv a '' D) :
    IsCompact (chartPt a '' K) ∧ chartPt a '' K ⊆ D ∧
      chartInv a '' (chartPt a '' K) = K := by
  have hKs : K ⊆ (extChartAt (ComplexModel n) a).source :=
    hKW.trans (inverse_image_subset_source a hDt)
  refine ⟨hK.image_of_continuousOn
    ((continuousOn_extChartAt (I := ComplexModel n) a).mono hKs), ?_, ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hKW hx
    simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).right_inv (hDt hw)] using hw
  · apply Subset.antisymm
    · rintro x ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).left_inv (hKs hy)] using hy
    · intro x hx
      exact ⟨chartPt a x, mem_image_of_mem _ hx,
        (extChartAt (ComplexModel n) a).left_inv (hKs hx)⟩

theorem eventually_aemeasurable_on_compact
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {K : Set M.Carrier} (hK : IsCompact K)
    (μ : Measure M.Carrier) :
    ∀ᶠ j in atTop, AEMeasurable (us (φ j)) (μ.restrict K) := by
  obtain ⟨N, hN⟩ := D04Aux.compact_eventually_subset_subsequence hΩ hcover hK hφ
  filter_upwards [eventually_ge_atTop N] with j hj
  exact aemeasurable_restrict_of_measurable_subtype hK.measurableSet
    (upperSemicontinuousOn_iff_restrict.mpr ((hpsh (φ j)).2.1.mono (hN j hj))).measurable

/-- Certified local output on one original chart, after transporting only
the original representative and original errors by the volume law. -/
structure ChartLimit (μ : Measure M.Carrier) (a : M.Carrier)
    (D : Set (ComplexVector n)) (us : ℕ → M.Carrier → EReal) (φ : ℕ → ℕ) where
  value : M.Carrier → EReal
  usc : UpperSemicontinuous value
  psh : IsPshOn (fun z => value (chartInv a z)) D
  lt_top : ∀ x ∈ chartInv a '' D, value x < ⊤
  finite : ∀ K : Set M.Carrier, IsCompact K → K ⊆ chartInv a '' D →
    ∀ᵐ x ∂μ.restrict K, value x ≠ ⊥ ∧ value x ≠ ⊤
  integrable : ∀ K : Set M.Carrier, IsCompact K → K ⊆ chartInv a '' D →
    IntegrableOn (fun x => (value x).toReal) K μ
  convergence : ∀ K : Set M.Carrier, IsCompact K → K ⊆ chartInv a '' D →
    Tendsto (fun j => ∫⁻ x in K, erealDist (us (φ j) x) (value x) ∂μ) atTop (𝓝 0)
  hartogs : ∀ c : ℝ, (∀ x ∈ chartInv a '' D, value x = c) →
    ∀ K : Set M.Carrier, IsCompact K → K ⊆ chartInv a '' D →
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ j, N ≤ j → ∀ x ∈ K, us (φ j) x ≤ ((c + ε : ℝ) : EReal)

theorem chartLimit_of_coordinate_limit
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {D : Set (ComplexVector n)} (hD : IsOpen D) (hDt : D ⊆ chartTarget a)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlimit : PshL1Limit D (fun j z => us j (chartInv a z)) φ) :
    Nonempty (ChartLimit μ a D us φ) := by
  obtain ⟨v, hv, _, hvfinite, hvlocal, hhartogs⟩ := hlimit
  let p := chartPotential a D v
  have hp : UpperSemicontinuous p := upperSemicontinuous_chartPotential a hD hDt hv.2.1
  have hpeq : EqOn (fun z => p (chartInv a z)) v D :=
    fun z hz => chartPotential_inverse a hDt v hz
  refine ⟨⟨p, hp, isPshOn_congr hv hpeq, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro x ⟨z, hz, rfl⟩
    exact (hpeq hz).trans_lt (hv.1 z hz)
  · intro K hK hKW
    obtain ⟨hL, hLD, hLK⟩ := chart_compact_coordinates a hDt hK hKW
    rw [← hLK]
    exact chartPotential_finite_ae g hg μ hμ a hD hDt hL hLD hv hvfinite
  · intro K hK hKW
    obtain ⟨hL, hLD, hLK⟩ := chart_compact_coordinates a hDt hK hKW
    rw [← hLK]
    exact chartPotential_integrableOn g hg μ hμ a hD hDt hL hLD hv (hvlocal _ hLD hL).1
  · intro K hK hKW
    obtain ⟨hL, hLD, hLK⟩ := chart_compact_coordinates a hDt hK hKW
    have hmeas : ∀ᶠ j in atTop,
        AEMeasurable (fun x => erealDist (us (φ j) x) (p x)) (μ.restrict K) :=
      (eventually_aemeasurable_on_compact Ωs us hΩ hcover hpsh hφ hK μ).mono
        (fun j hj => aemeasurable_erealDist hj hp.measurable.aemeasurable)
    have heq (j : ℕ) : (∫⁻ z in chartPt a '' K,
        erealDist (us (φ j) (chartInv a z)) (p (chartInv a z)) ∂lebesgueC n) =
        ∫⁻ z in chartPt a '' K, erealDist (us (φ j) (chartInv a z)) (v z) ∂lebesgueC n := by
      apply setLIntegral_congr_fun hL.measurableSet
      intro z hz
      dsimp only
      exact congrArg (fun t => erealDist (us (φ j) (chartInv a z)) t) (hpeq (hLD hz))
    have hcoordconv : Tendsto (fun j => ∫⁻ z in chartPt a '' K,
        erealDist (us (φ j) (chartInv a z)) (p (chartInv a z)) ∂lebesgueC n) atTop (𝓝 0) := by
      simp_rw [heq]
      exact (hvlocal _ hLD hL).2
    rw [← hLK] at hmeas ⊢
    exact tendsto_lintegral_chart_compact_of_coordinate g hg μ hμ a hL (hLD.trans hDt)
      (fun j x => erealDist (us (φ j) x) (p x)) hmeas hcoordconv
  · intro c hc K hK hKW ε hε
    obtain ⟨hL, hLD, hLK⟩ := chart_compact_coordinates a hDt hK hKW
    have hvc : ∀ z ∈ D, v z = c := by
      intro z hz
      rw [← hpeq hz]
      exact hc _ (mem_image_of_mem _ hz)
    obtain ⟨N, hN⟩ := hhartogs c hvc _ hLD hL ε hε
    refine ⟨N, ?_⟩
    intro j hj x hx
    have hxsource := inverse_image_subset_source a hDt (hKW hx)
    simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).left_inv hxsource] using
      hN j hj (chartPt a x) (mem_image_of_mem _ hx)

end Yau.Proofs.D04AtlasGlueAux
