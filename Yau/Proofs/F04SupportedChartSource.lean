import Yau.Proofs.F04SupportedL2Pairing
import Yau.Proofs.F03ScalarL2Pairing
import Yau.LeafProofs.L19HeatRegularityChart

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual local chart of a supported physical source is exactly its
 original physical function pulled into that chart. Actual-volume AE
 equalities are transported by the native computed positive chart density;
 no pointwise representative of an L2 class is assumed canonical. -/
theorem supportedL2_physical_chart_source
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω)
    {f : M.Carrier → ℝ} (hf : ScalarL2 (μ.restrict Ω) f) :
    scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ (scalarToLp hf))
      =ᵐ[volume.restrict O] (fun z => f (chartInv c z)) := by
  have hInd : Ω.indicator (scalarToLp hf : M.Carrier → ℝ) =ᵐ[μ] Ω.indicator f :=
    (ae_eq_restrict_iff_indicator_ae_eq hΩ).mp (scalarToLp_coe hf)
  have hZ : (l2ZeroExtension μ Ω hΩ (scalarToLp hf) : M.Carrier → ℝ) =ᵐ[μ] Ω.indicator f :=
    (extendL2_coe μ Ω hΩ (scalarToLp hf)).trans hInd
  have hPull := scalarEnergy_chart_ae_eq g μ hμ c hO hOC hOt hZ
  have hR := scalarEnergy_chartRestrictionCLM_coe g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ (scalarToLp hf))
  filter_upwards [hR, hPull, ae_restrict_mem hO.measurableSet] with z hz hp hzO
  rw [hz, hp, indicator_of_mem (hMap ⟨z, hzO, rfl⟩)]

end Yau.F04Proof
