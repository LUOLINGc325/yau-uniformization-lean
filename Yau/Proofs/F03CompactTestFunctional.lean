import Yau.Proofs.F03RegularClosedMeasure

/-! Genuine bounded continuous-function test pairings on compact cylinders. -/
noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux

/-- Restriction uses actual continuity on the compact set. -/
def compactContinuousRestriction {E : Type*} [TopologicalSpace E]
    (K : Set E) (f : E → ℝ) (hf : ContinuousOn f K) : C(K,ℝ) :=
  ⟨fun x => f x,continuousOn_iff_continuous_restrict.mp hf⟩

/-- Every actual compact continuous test gives a bounded linear functional
on the genuine Banach space C(K), through its actual finite-measure L² map. -/
def compactTestFunctional {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (K : Set E) [CompactSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (φ : C(K,ℝ)) : C(K,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (ContinuousMap.toLp 2 ν ℝ φ)).comp (ContinuousMap.toLp 2 ν ℝ)

theorem compactTestFunctional_apply {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (K : Set E) [CompactSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (φ q : C(K,ℝ)) : compactTestFunctional K ν φ q = ∫ x, q x * φ x ∂ν := by
  change inner ℝ (ContinuousMap.toLp 2 ν ℝ φ) (ContinuousMap.toLp 2 ν ℝ q) = _
  simpa only [conj_trivial] using ContinuousMap.inner_toLp (μ := ν) φ q

/-- The compact-cylinder test pairing is exactly the original ambient
restricted integral of the actual functions. -/
theorem compactTestFunctional_restrict_apply {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (K : Set E)
    [CompactSpace K] (hK : MeasurableSet K)
    [IsFiniteMeasure (μ.comap ((↑) : K → E))]
    (φ f : E → ℝ) (hφ : ContinuousOn φ K) (hf : ContinuousOn f K) :
    compactTestFunctional K (μ.comap ((↑) : K → E))
      (compactContinuousRestriction K φ hφ) (compactContinuousRestriction K f hf) =
        ∫ x in K, f x * φ x ∂μ := by
  rw [compactTestFunctional_apply]
  exact integral_subtype_comap hK (fun x => f x * φ x)

end Yau.Proofs.F03Aux
