import Yau.Proofs.D04AtlasGlueLocal
import Yau.Proofs.D04GlueTools

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_compact_positive_subset
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) {U : Set M.Carrier} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ K : Set M.Carrier, IsCompact K ∧ K ⊆ U ∧ 0 < μ K := by
  obtain ⟨a, ha⟩ := hUne
  let O := chartTarget a ∩ chartInv a ⁻¹' U
  have hO : IsOpen O :=
    (continuousOn_extChartAt_symm (I := ComplexModel n) a).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := ComplexModel n) a) hU
  have hcenter : chartPt a a ∈ O := by
    refine ⟨mem_extChartAt_target a, ?_⟩
    simpa only [mem_preimage, chartPt, chartInv,
      (extChartAt (ComplexModel n) a).left_inv (mem_extChartAt_source a)] using ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hcenter)
  let L := Metric.closedBall (chartPt a a) (r / 2)
  have hLO : L ⊆ O := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hLt : L ⊆ chartTarget a := hLO.trans inter_subset_left
  refine ⟨chartInv a '' L, (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hLt), ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact (hLO hz).2
  · apply measure_chart_compact_pos g hg μ hμ a (isCompact_closedBall _ _) hLt
    rw [lebesgueC_eq_volume]
    exact Metric.measure_closedBall_pos volume _ (half_pos hr)

def CollapsesOn (U : Set M.Carrier) (us : ℕ → M.Carrier → EReal) (φ : ℕ → ℕ) : Prop :=
  ∀ K : Set M.Carrier, IsCompact K → K ⊆ U → ∀ A : ℝ,
    ∃ N, ∀ j, N ≤ j → ∀ x ∈ K, us (φ j) x ≤ ((-A : ℝ) : EReal)

theorem collapsesOn_of_coordinate
    (a : M.Carrier) {D : Set (ComplexVector n)} (hDt : D ⊆ chartTarget a)
    {us : ℕ → M.Carrier → EReal} {φ : ℕ → ℕ}
    (hcollapse : PshCollapses D (fun j z => us j (chartInv a z)) φ) :
    CollapsesOn (chartInv a '' D) us φ := by
  intro K hK hKW A
  obtain ⟨hL, hLD, _⟩ := chart_compact_coordinates a hDt hK hKW
  obtain ⟨N, hN⟩ := hcollapse _ hLD hL A
  refine ⟨N, ?_⟩
  intro j hj x hx
  have hxs := inverse_image_subset_source a hDt (hKW hx)
  simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).left_inv hxs] using
    hN j hj (chartPt a x) (mem_image_of_mem _ hx)

theorem collapse_limit_overlap_empty
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {U : Set M.Carrier} (hU : IsOpen U) (hcollapse : CollapsesOn U us φ)
    (a : M.Carrier) {D : Set (ComplexVector n)}
    (hD : IsOpen D) (hDt : D ⊆ chartTarget a)
    (L : ChartLimit μ a D us φ) : Disjoint U (chartInv a '' D) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨K, hK, hKU, hKpos⟩ := exists_compact_positive_subset g hg μ hμ
    (hU.inter (isOpen_chart_image a hD hDt)) (Set.nonempty_iff_ne_empty.mpr hne)
  have hKL : K ⊆ chartInv a '' D := hKU.trans inter_subset_right
  apply not_collapse_on_positive_mass hK.measurableSet hKpos (L.finite K hK hKL)
    ((eventually_aemeasurable_on_compact Ωs us hΩ hcover hpsh hφ hK μ).mono
      (fun j hj => aemeasurable_erealDist hj L.usc.measurable.aemeasurable))
    (L.convergence K hK hKL)
  exact hcollapse K hK (hKU.trans inter_subset_left)

/-- A chart psh function is bounded pointwise by a globally USC potential
when the same inequality holds on every compact with the original volume. -/
theorem chart_comparison
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {D : Set (ComplexVector n)} (hD : IsOpen D) (hDt : D ⊆ chartTarget a)
    {p q : M.Carrier → EReal} (hp : IsPshOn (fun z => p (chartInv a z)) D)
    (hq : UpperSemicontinuous q)
    {U : Set M.Carrier} (hU : IsOpen U) (hUW : U ⊆ chartInv a '' D)
    (hae : ∀ K : Set M.Carrier, IsCompact K → K ⊆ U → ∀ᵐ x ∂μ.restrict K, p x ≤ q x) :
    ∀ x ∈ U, p x ≤ q x := by
  let O := D ∩ chartInv a ⁻¹' U
  have hO : IsOpen O :=
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hDt).isOpen_inter_preimage hD hU
  have hOD : O ⊆ D := inter_subset_left
  have hpO := D04Aux.isPshOn_mono hp hOD
  have hqO : UpperSemicontinuousOn (fun z => q (chartInv a z)) O :=
    (upperSemicontinuousOn_univ_iff.mpr hq).comp
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hOD.trans hDt))
      (fun _ _ => mem_univ _)
  have haeO : ∀ᵐ z ∂volume.restrict O, p (chartInv a z) ≤ q (chartInv a z) := by
    apply D04Aux.ae_on_open_of_ae_on_compacts hO
    intro K hK hKO
    have hKt := hKO.trans (hOD.trans hDt)
    have hiK := hK.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hKt)
    have hiKU : chartInv a '' K ⊆ U := by
      rintro x ⟨z, hz, rfl⟩
      exact (hKO hz).2
    simpa only [lebesgueC_eq_volume] using
      ae_chart_compact_pullback g hg μ hμ a hK hKt (hae _ hiK hiKU)
  intro x hx
  have hxs := inverse_image_subset_source a hDt (hUW hx)
  have hzD : chartPt a x ∈ D := by
    obtain ⟨z, hz, rfl⟩ := hUW hx
    simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).right_inv (hDt hz)] using hz
  have hzO : chartPt a x ∈ O := by
    refine ⟨hzD, ?_⟩
    simpa only [mem_preimage, chartPt, chartInv, (extChartAt (ComplexModel n) a).left_inv hxs] using hx
  simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).left_inv hxs] using
    D04Aux.psh_le_usc_of_ae_le hO hpO hqO haeO (chartPt a x) hzO

theorem chartLimits_agree
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (a b : M.Carrier) {D E : Set (ComplexVector n)}
    (hD : IsOpen D) (hDt : D ⊆ chartTarget a)
    (hE : IsOpen E) (hEt : E ⊆ chartTarget b)
    (L : ChartLimit μ a D us φ) (R : ChartLimit μ b E us φ) :
    EqOn L.value R.value ((chartInv a '' D) ∩ (chartInv b '' E)) := by
  have hae (K : Set M.Carrier) (hK : IsCompact K)
      (hKU : K ⊆ (chartInv a '' D) ∩ (chartInv b '' E)) : L.value =ᵐ[μ.restrict K] R.value :=
    limits_unique_of_erealDist
      (eventually_aemeasurable_on_compact Ωs us hΩ hcover hpsh hφ hK μ)
      L.usc.measurable.aemeasurable R.usc.measurable.aemeasurable
      (L.convergence K hK (hKU.trans inter_subset_left))
      (R.convergence K hK (hKU.trans inter_subset_right))
  have hU := (isOpen_chart_image a hD hDt).inter (isOpen_chart_image b hE hEt)
  intro x hx
  exact le_antisymm
    (chart_comparison g hg μ hμ a hD hDt L.psh R.usc hU inter_subset_left
      (fun K hK hKU => (hae K hK hKU).mono (fun _ h => h.le)) x hx)
    (chart_comparison g hg μ hμ b hE hEt R.psh L.usc hU inter_subset_right
      (fun K hK hKU => (hae K hK hKU).mono (fun _ h => h.ge)) x hx)

end Yau.Proofs.D04AtlasGlueAux
