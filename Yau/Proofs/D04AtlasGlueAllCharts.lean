import Yau.Proofs.D04AtlasGlueTopology

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- A global finite local-L1 limit that is psh in its selected charts is
psh in every connected portion of every original chart. The only producer
used is the same original coordinate bridge, applied to the global sequence. -/
theorem psh_in_original_chart
    (hcoord : PshCompactnessBridge n)
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    (hupper : ∀ K : Set M.Carrier, IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Ωs j → ∀ x ∈ K, us j x ≤ (C : EReal))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {u : M.Carrier → EReal} (hu : ∀ x, u x < ⊤) (husc : UpperSemicontinuous u)
    (hfinite : ∀ᵐ x ∂μ, u x ≠ ⊥)
    (hconv : ∀ K : Set M.Carrier, IsCompact K →
      Tendsto (fun j => ∫⁻ x in K, erealDist (us (φ j) x) (u x) ∂μ) atTop (𝓝 0))
    (hselected : ∀ x : M.Carrier, ∃ (b : M.Carrier) (E : Set (ComplexVector n)),
      IsOpen E ∧ E ⊆ chartTarget b ∧ x ∈ chartInv b '' E ∧
        IsPshOn (fun z => u (chartInv b z)) E)
    (a : M.Carrier) (D : Set (ComplexVector n))
    (hD : IsOpen D) (hconn : IsConnected D) (hDt : D ⊆ chartTarget a) :
    IsPshOn (fun z => u (chartInv a z)) D := by
  obtain ⟨τ, hτ, hbranch⟩ := coordinate_extraction hcoord a D hD hconn hDt
    Ωs us hΩ hcover hpsh hupper φ hφ
  let ψ := φ ∘ τ
  have hψ : StrictMono ψ := hφ.comp hτ
  have hconvψ (K : Set M.Carrier) (hK : IsCompact K) :
      Tendsto (fun j => ∫⁻ x in K, erealDist (us (ψ j) x) (u x) ∂μ) atTop (𝓝 0) := by
    simpa only [ψ, Function.comp_def] using (hconv K hK).comp hτ.tendsto_atTop
  have hL : Nonempty (ChartLimit μ a D us ψ) := by
    rcases hbranch with hc | hl
    · have hc' : PshCollapses D (fun j z => us j (chartInv a z)) ψ := by
        simpa only [PshCollapses, ψ, Function.comp_def] using hc
      have hcollapse := collapsesOn_of_coordinate a hDt hc'
      obtain ⟨z, hz⟩ := hconn.1
      obtain ⟨K, hK, hKW, hKpos⟩ := exists_compact_positive_subset g hg μ hμ
        (isOpen_chart_image a hD hDt) ⟨chartInv a z, mem_image_of_mem _ hz⟩
      exfalso
      apply not_collapse_on_positive_mass hK.measurableSet hKpos
        ((ae_restrict_of_ae hfinite).mono (fun x hx => ⟨hx, (hu x).ne⟩))
        ((eventually_aemeasurable_on_compact Ωs us hΩ hcover hpsh hψ hK μ).mono
          (fun j hj => aemeasurable_erealDist hj husc.measurable.aemeasurable))
        (hconvψ K hK)
      exact hcollapse K hK hKW
    · have hl' : PshL1Limit D (fun j z => us j (chartInv a z)) ψ := by
        simpa only [PshL1Limit, ψ, Function.comp_def] using hl
      exact chartLimit_of_coordinate_limit g hg μ hμ a hD hDt Ωs us hΩ hcover hpsh hψ hl'
  obtain ⟨L⟩ := hL
  have hae (K : Set M.Carrier) (hK : IsCompact K) (hKW : K ⊆ chartInv a '' D) :
      L.value =ᵐ[μ.restrict K] u :=
    limits_unique_of_erealDist
      (eventually_aemeasurable_on_compact Ωs us hΩ hcover hpsh hψ hK μ)
      L.usc.measurable.aemeasurable husc.measurable.aemeasurable
      (L.convergence K hK hKW) (hconvψ K hK)
  have hle : ∀ x ∈ chartInv a '' D, L.value x ≤ u x :=
    chart_comparison g hg μ hμ a hD hDt L.psh husc
      (isOpen_chart_image a hD hDt) subset_rfl
      (fun K hK hKW => (hae K hK hKW).mono (fun _ h => h.le))
  have heq : EqOn L.value u (chartInv a '' D) := by
    intro x hx
    obtain ⟨b, E, hE, hEt, hxE, hupsh⟩ := hselected x
    have hU := (isOpen_chart_image a hD hDt).inter (isOpen_chart_image b hE hEt)
    apply le_antisymm (hle x hx)
    exact chart_comparison g hg μ hμ b hE hEt hupsh L.usc hU inter_subset_right
      (fun K hK hKU => (hae K hK (hKU.trans inter_subset_left)).mono (fun _ h => h.ge))
      x ⟨hx, hxE⟩
  apply isPshOn_congr L.psh
  intro z hz
  exact (heq (mem_image_of_mem _ hz)).symm

/-- The original `IsPsh` quantifier over every chart and every full closed
affine disc follows directly, without any new chart-invariance assumption. -/
theorem isPsh_of_selected_atlas_limit
    (hcoord : PshCompactnessBridge n)
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    (hupper : ∀ K : Set M.Carrier, IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Ωs j → ∀ x ∈ K, us j x ≤ (C : EReal))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {u : M.Carrier → EReal} (hu : ∀ x, u x < ⊤) (husc : UpperSemicontinuous u)
    (hfinite : ∀ᵐ x ∂μ, u x ≠ ⊥)
    (hconv : ∀ K : Set M.Carrier, IsCompact K →
      Tendsto (fun j => ∫⁻ x in K, erealDist (us (φ j) x) (u x) ∂μ) atTop (𝓝 0))
    (hselected : ∀ x : M.Carrier, ∃ (b : M.Carrier) (E : Set (ComplexVector n)),
      IsOpen E ∧ E ⊆ chartTarget b ∧ x ∈ chartInv b '' E ∧
        IsPshOn (fun z => u (chartInv b z)) E) : IsPsh u := by
  refine ⟨hu, husc, ?_⟩
  intro a z w hdisc f hf hmajor
  obtain ⟨hD, hconn, hdiscD⟩ := closed_disc_subset_chart_component a z w hdisc
  have hp := psh_in_original_chart hcoord g hg μ hμ Ωs us hΩ hcover hpsh hupper
    hφ hu husc hfinite hconv hselected a (connectedComponentIn (chartTarget a) z)
    hD hconn (connectedComponentIn_subset _ _)
  exact hp.2.2 z w hdiscD f hf hmajor

end Yau.Proofs.D04AtlasGlueAux
