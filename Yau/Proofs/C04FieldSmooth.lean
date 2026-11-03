import Yau.Proofs.C04ClockBasic

/-! Slice regularity of the original localized flow and density. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem field_metricSmooth_at_time (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I) {t : ℝ} (ht : t ∈ I) : MetricSmooth (h t) := by
  intro x a b
  exact (hh x a b).comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun z hz => ⟨hz, ht⟩)

theorem spaceSlice_smoothFn {f : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hf : SmoothSpaceTime f I) {t : ℝ} (ht : t ∈ I) : SmoothFn (fun x => f x t) := by
  intro x
  exact (hf x).comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun z hz => ⟨hz, ht⟩)

theorem localizedFlow_metricSmooth (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) : MetricSmooth (h t) :=
  field_metricSmooth_at_time h hf.1.2.1 ht

theorem localizedFlow_rho_continuous (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) : Continuous (fun x => ρ x t) :=
  LeafProofs.L18Aux.continuous_of_smoothFn (spaceSlice_smoothFn hf.2.2.2.1 ht)

theorem localizedFlow_rho_compact_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ x ∈ K, |ρ x t| ≤ C := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image
    (localizedFlow_rho_continuous X o h U P ρ hf ht).abs.continuousOn
  exact ⟨C, fun x hx => hC (Set.mem_image_of_mem _ hx)⟩

end Yau.Proofs.C04Aux
