import Yau.Proofs.F04ProductSliceEquality
import Yau.LeafProofs.L19HeatRegularityChart

open MeasureTheory Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.LeafProofs.L19Aux

/-- Any actual-volume almost-everywhere scalar order transports to the
 genuine coordinate volume inside a supported chart. The native chart
 density transports the proposition itself; no regularity of either
 scalar or arbitrary representative is required. -/
theorem chart_ae_le_of_supported_ae_le
    {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω)
    {f k : M.Carrier → ℝ} (hfk : f ≤ᵐ[μ.restrict Ω] k) :
    (fun z => f (chartInv c z)) ≤ᵐ[volume.restrict O] (fun z => k (chartInv c z)) := by
  have hProp : (fun x => x ∈ Ω → f x ≤ k x) =ᵐ[μ] (fun _ => True) := by
    filter_upwards [(ae_restrict_iff' hΩ).mp hfk] with x hx
    exact propext ⟨fun _ => trivial, fun _ => hx⟩
  have hPull := scalarEnergy_chart_ae_eq g μ hμ c hO hOC hOt hProp
  filter_upwards [hPull, ae_restrict_mem hO.measurableSet] with z hz hzO
  have hh : chartInv c z ∈ Ω → f (chartInv c z) ≤ k (chartInv c z) := hz.mpr trivial
  exact hh (hMap ⟨z,hzO,rfl⟩)

/-- Slice order becomes genuine product order by Fubini on the actual
 L2 norm of the difference; no measurable pointwise evaluation of an
 abstract L2-valued path is assumed. -/
theorem product_memLp_ae_le_of_ae_time_slices
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f g : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν))
    (hSlices : ∀ᵐ t ∂ν, (fun x => f (x,t)) ≤ᵐ[μ] (fun x => g (x,t))) :
    f ≤ᵐ[μ.prod ν] g := by
  have hD := hg.sub hf
  have hEq : (fun p => ‖g p - f p‖) =ᵐ[μ.prod ν] (fun p => g p - f p) := by
    apply product_memLp_ae_eq_of_ae_time_slices hD.norm hD
    filter_upwards [hSlices] with t ht
    filter_upwards [ht] with x hx
    exact Real.norm_of_nonneg (sub_nonneg.mpr hx)
  filter_upwards [hEq] with p hp
  have hn := norm_nonneg (g p - f p)
  rw [hp] at hn
  exact sub_nonneg.mp hn

/-- Continuous classical representatives inherit actual almost-everywhere
 order at EVERY point of an open coordinate set. -/
theorem continuousOn_le_of_ae_le
    {n : ℕ} {Q : Set (Yau.Parabolic.Point n)} (hQ : IsOpen Q)
    {f g : Yau.Parabolic.Point n → ℝ}
    (hf : ContinuousOn f Q) (hg : ContinuousOn g Q)
    (hfg : f ≤ᵐ[(volume : Measure (Yau.Parabolic.Point n)).restrict Q] g) : ∀ p ∈ Q, f p ≤ g p := by
  have hAE : (fun p => |g p - f p|) =ᵐ[(volume : Measure (Yau.Parabolic.Point n)).restrict Q]
      (fun p => g p - f p) := by
    filter_upwards [hfg] with p hp
    exact abs_of_nonneg (sub_nonneg.mpr hp)
  have hEq := Measure.eqOn_open_of_ae_eq hAE hQ (hg.sub hf).abs (hg.sub hf)
  intro p hp
  exact sub_nonneg.mp (abs_eq_self.mp (hEq hp))

end Yau.F04Proof
