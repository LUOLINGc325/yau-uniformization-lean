import Yau.Proofs.P03CompactPairing

open scoped Topology
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {K P : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [CompactSpace K] [TopologicalSpace P] (μ : Measure K) [IsFiniteMeasure μ]

def compactIntegralCLM : C(K, ℂ) →L[ℂ] ℂ :=
  compactPairingCLM μ (ContinuousMap.id K) 1

theorem compactIntegralCLM_apply (f : C(K, ℂ)) :
    compactIntegralCLM μ f = ∫ z, f z ∂μ := by
  rw [compactIntegralCLM, compactPairingCLM_apply]
  simp only [ContinuousMap.one_apply, one_mul, ContinuousMap.id_apply]

/-- Compact integration is continuous for a jointly continuous family,
with no local compactness assumption on its parameter space. -/
theorem continuous_integral_compact_family (F : P → C(K, ℂ))
    (hF : Continuous (Function.uncurry fun p z => F p z)) :
    Continuous (fun p => ∫ z, F p z ∂μ) := by
  have hc := (compactIntegralCLM μ).continuous.comp
    (ContinuousMap.continuous_of_continuous_uncurry F hF)
  exact hc.congr (fun p => compactIntegralCLM_apply μ (F p))

end Yau.NodeProofs.P03Aux
