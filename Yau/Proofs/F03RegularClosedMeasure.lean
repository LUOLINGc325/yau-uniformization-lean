import Yau.Proofs.F03ScalarL2

/-! Actual full-support and finiteness of compact cylinder subtype measures. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux

/-- Pullback to a regular closed set has full relative support. This uses
the density of its actual interior and positivity on ambient open sets. -/
theorem comap_subtype_isOpenPosMeasure_of_regularClosed
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsOpenPosMeasure] (K : Set E) (hK : MeasurableSet K)
    (hreg : K = closure (interior K)) :
    (μ.comap ((↑) : K → E)).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [comap_subtype_coe_apply hK]
  obtain ⟨O,hO,hOU⟩ := (isOpen_induced_iff (f := ((↑) : K → E))).mp hU
  obtain ⟨x,hx⟩ := hUne
  have hxO : (x : E) ∈ O := by
    change x ∈ ((↑) : K → E) ⁻¹' O
    rw [hOU]
    exact hx
  have hxK : (x : E) ∈ closure (interior K) := by
    rw [← hreg]
    exact x.property
  have hNon : (O ∩ interior K).Nonempty := mem_closure_iff.mp hxK O hO hxO
  have hsub : O ∩ interior K ⊆ ((↑) : K → E) '' U := by
    intro y hy
    refine ⟨⟨y,interior_subset hy.2⟩,?_,rfl⟩
    rw [← hOU]
    exact hy.1
  exact (lt_of_lt_of_le ((hO.inter isOpen_interior).measure_pos μ hNon) (measure_mono hsub)).ne'

/-- Finite actual ambient measure transfers to the literal subtype measure. -/
theorem comap_subtype_isFiniteMeasure_of_measure_lt_top
    {E : Type*} [MeasurableSpace E] (μ : Measure E) (K : Set E)
    (hK : MeasurableSet K) (hfin : μ K < ⊤) :
    IsFiniteMeasure (μ.comap ((↑) : K → E)) := by
  constructor
  rw [comap_subtype_coe_apply hK]
  simpa only [image_univ,Subtype.range_coe] using hfin

end Yau.Proofs.F03Aux
