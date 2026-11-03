import Yau.Proofs.D04AtlasGlueCover
import Yau.Proofs.D04AtlasGlueVolumeCompare

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

theorem isOpen_chart_image (a : M.Carrier) {D : Set (ComplexVector n)}
    (hD : IsOpen D) (hDt : D ⊆ chartTarget a) : IsOpen (chartInv a '' D) := by
  change IsOpen ((extChartAt (ComplexModel n) a).symm '' D)
  rw [(extChartAt (ComplexModel n) a).symm_image_eq_source_inter_preimage hDt]
  exact isOpen_extChartAt_preimage' (I := ComplexModel n) a hD

/-- A local representative is extended by top outside its open chart image.
The extension is globally USC, while its values on that image are unchanged. -/
def chartPotential (a : M.Carrier) (D : Set (ComplexVector n))
    (v : ComplexVector n → EReal) (x : M.Carrier) : EReal := by
  classical
  exact if x ∈ chartInv a '' D then v (chartPt a x) else ⊤

theorem chartPotential_inverse (a : M.Carrier) {D : Set (ComplexVector n)}
    (hDt : D ⊆ chartTarget a) (v : ComplexVector n → EReal)
    {z : ComplexVector n} (hz : z ∈ D) :
    chartPotential a D v (chartInv a z) = v z := by
  simp only [chartPotential, ite_eq_left (mem_image_of_mem (chartInv a) hz)]
  rw [show chartPt a (chartInv a z) = z from
    (extChartAt (ComplexModel n) a).right_inv (hDt hz)]

theorem upperSemicontinuousOn_chart_pullback (a : M.Carrier)
    {D : Set (ComplexVector n)} (hDt : D ⊆ chartTarget a)
    {v : ComplexVector n → EReal} (hv : UpperSemicontinuousOn v D) :
    UpperSemicontinuousOn (fun x => v (chartPt a x)) (chartInv a '' D) := by
  apply hv.comp
    ((continuousOn_extChartAt (I := ComplexModel n) a).mono (inverse_image_subset_source a hDt))
  rintro x ⟨z, hz, rfl⟩
  simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).right_inv (hDt hz)] using hz

theorem upperSemicontinuous_chartPotential (a : M.Carrier)
    {D : Set (ComplexVector n)} (hD : IsOpen D) (hDt : D ⊆ chartTarget a)
    {v : ComplexVector n → EReal} (hv : UpperSemicontinuousOn v D) :
    UpperSemicontinuous (chartPotential a D v) := by
  classical
  have hW := isOpen_chart_image a hD hDt
  have hlocal := upperSemicontinuousOn_chart_pullback a hDt hv
  intro x b hxb
  by_cases hx : x ∈ chartInv a '' D
  · have hxb' : v (chartPt a x) < b := by simpa only [chartPotential, ite_eq_left hx] using hxb
    have hevent := hlocal x hx b hxb'
    rw [hW.nhdsWithin_eq hx] at hevent
    filter_upwards [hW.mem_nhds hx, hevent] with y hy hyb
    simpa only [chartPotential, ite_eq_left hy] using hyb
  · have : (⊤ : EReal) < b := by simpa only [chartPotential, ite_eq_right hx] using hxb
    exact (not_top_lt this).elim

theorem ae_chart_compact_pushforward
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    {P : M.Carrier → Prop} (hPm : MeasurableSet {x | P x})
    (hP : ∀ᵐ z ∂(lebesgueC n).restrict K, P (chartInv a z)) :
    ∀ᵐ x ∂μ.restrict (chartInv a '' K), P x := by
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))
      ((lebesgueC n).restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((volumeDensity_continuousOn g hg a).mono hKt).aemeasurable hK.measurableSet)
  rw [riemannianVolume_restrict_chart_compact g μ hμ a hK hKt]
  apply (ae_map_iff (L18Aux.chartInvExtension_measurable a).aemeasurable hPm).mpr
  apply (ae_withDensity_iff' hd).mpr
  filter_upwards [hP, ae_restrict_mem hK.measurableSet] with z hz hzK
  intro _
  simpa only [L18Aux.chartInvExtension, ite_eq_left (hKt hzK)] using hz

/-- Finite-a.e. local representatives retain their actual EReal values
when transported to the original manifold volume. -/
theorem chartPotential_finite_ae
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {D K : Set (ComplexVector n)} (hD : IsOpen D) (hDt : D ⊆ chartTarget a)
    (hK : IsCompact K) (hKD : K ⊆ D)
    {v : ComplexVector n → EReal} (hv : IsPshOn v D)
    (hfinite : ∀ᵐ z ∂(lebesgueC n).restrict D, v z ≠ ⊥) :
    ∀ᵐ x ∂μ.restrict (chartInv a '' K),
      chartPotential a D v x ≠ ⊥ ∧ chartPotential a D v x ≠ ⊤ := by
  have hm := (upperSemicontinuous_chartPotential a hD hDt hv.2.1).measurable
  apply ae_chart_compact_pushforward g hg μ hμ a hK (hKD.trans hDt)
    (((hm (measurableSet_singleton ⊥)).compl).inter ((hm (measurableSet_singleton ⊤)).compl))
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hKD hfinite,
    ae_restrict_mem hK.measurableSet] with z hz hzK
  change chartPotential a D v (chartInv a z) ≠ ⊥ ∧
    chartPotential a D v (chartInv a z) ≠ ⊤
  rw [chartPotential_inverse a hDt v (hKD hzK)]
  exact ⟨hz, (hv.1 z (hKD hzK)).ne⟩

/-- The bounded positive chart density transports genuine local real
integrability of the same EReal representative. -/
theorem chartPotential_integrableOn
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {D K : Set (ComplexVector n)} (hD : IsOpen D) (hDt : D ⊆ chartTarget a)
    (hK : IsCompact K) (hKD : K ⊆ D)
    {v : ComplexVector n → EReal} (hv : IsPshOn v D)
    (hi : IntegrableOn (fun z => (v z).toReal) K (lebesgueC n)) :
    IntegrableOn (fun x => (chartPotential a D v x).toReal) (chartInv a '' K) μ := by
  have hm := (upperSemicontinuous_chartPotential a hD hDt hv.2.1).measurable.ereal_toReal
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  obtain ⟨c, C, hc, hC, hb⟩ :=
    lintegral_chart_compact_bounds g hg μ hμ a hK (hKD.trans hDt)
  have hbound := (hb (fun x => ‖(chartPotential a D v x).toReal‖ₑ) hm.enorm.aemeasurable).2
  have heq : (∫⁻ z in K, ‖(chartPotential a D v (chartInv a z)).toReal‖ₑ ∂lebesgueC n) =
      ∫⁻ z in K, ‖(v z).toReal‖ₑ ∂lebesgueC n := by
    apply setLIntegral_congr_fun hK.measurableSet
    intro z hz
    dsimp only
    rw [chartPotential_inverse a hDt v (hKD hz)]
  rw [heq] at hbound
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hi.hasFiniteIntegral)

end Yau.Proofs.D04AtlasGlueAux
