import Yau.Proofs.F04AdjointGlobal
import Yau.Proofs.F04Volume

/-! Compact Kähler adjoint for the actual, possibly incomplete evolving
metric, and the exact registered volume/adjoint target. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint
open Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem laplacian_congr_of_eventuallyEq (h : HermitianField M)
    {u v : M.Carrier → ℝ} {x : M.Carrier} (he : u =ᶠ[𝓝 x] v) :
    laplacian h u x = laplacian h v x := by
  exact congrArg (traceWith (gMat h x))
    (LeafProofs.L22Aux.levi_congr_of_eventuallyEq he)

theorem laplacian_zero_of_notMem_tsupport (h : HermitianField M)
    (u : M.Carrier → ℝ) {x : M.Carrier} (hx : x ∉ tsupport u) :
    laplacian h u x = 0 := by
  rw [laplacian_congr_of_eventuallyEq h (notMem_tsupport_iff_eventuallyEq.mp hx)]
  exact laplacian_const h 0 x

theorem compact_kahler_adjoint (g₀ : SmoothMetric M) (o : M.Carrier)
    (h : HermitianField M) (hh : MetricSmooth h) (hK : KahlerClosed h)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume h μ)
    (v ψ : M.Carrier → ℝ) (hv : SmoothFn v) (hψ : SmoothFn ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ x, ψ x * laplacian h v x ∂μ) = ∫ x, v x * laplacian h ψ x ∂μ := by
  obtain ⟨A, hA⟩ := (show IsCompact (tsupport ψ) from hcψ).bddAbove_image
    (LeafProofs.L12Aux.continuous_distFrom g₀ o).continuousOn
  let r : ℝ := max (A + 1) 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hAr : A < r := lt_of_lt_of_le (lt_add_one A) (le_max_left _ _)
  obtain ⟨κ, hκ, hcκ, _, hκone, _⟩ :=
    exists_smooth_compact_cutoff g₀ o hr (show r < r + 1 by linarith)
  have hκv : SmoothFn (fun x => κ x * v x) := smoothFn_mul hκ hv
  have hcκv : HasCompactSupport (fun x => κ x * v x) := hcκ.mul_right
  have hκvnear (x : M.Carrier) (hx : x ∈ tsupport ψ) :
      (fun y => κ y * v y) =ᶠ[𝓝 x] v := by
    have hdist : distFrom g₀.form o x < r := (hA ⟨x, hx, rfl⟩).trans_lt hAr
    have hnear : {y | distFrom g₀.form o y < r} ∈ 𝓝 x :=
      (LeafProofs.L12Aux.continuous_distFrom g₀ o).continuousAt.preimage_mem_nhds
        (Iio_mem_nhds hdist)
    filter_upwards [hnear] with y hy
    rw [hκone y hy.le, one_mul]
  have hleft : (∫ x, ψ x * laplacian h v x ∂μ) =
      ∫ x, ψ x * laplacian h (fun y => κ y * v y) x ∂μ := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change ψ x * laplacian h v x = ψ x * laplacian h (fun y => κ y * v y) x
    by_cases hx : x ∈ tsupport ψ
    · rw [laplacian_congr_of_eventuallyEq h (hκvnear x hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hright : (∫ x, (κ x * v x) * laplacian h ψ x ∂μ) =
      ∫ x, v x * laplacian h ψ x ∂μ := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change (κ x * v x) * laplacian h ψ x = v x * laplacian h ψ x
    by_cases hx : x ∈ tsupport ψ
    · rw [hκvnear x hx |>.eq_of_nhds]
    · rw [laplacian_zero_of_notMem_tsupport h ψ hx, mul_zero, mul_zero]
  calc
    (∫ x, ψ x * laplacian h v x ∂μ) =
        ∫ x, ψ x * laplacian h (fun y => κ y * v y) x ∂μ := hleft
    _ = -(1 / 2 : ℝ) * ∫ x, scalarGradientPair h ψ (fun y => κ y * v y) x ∂μ :=
      (Adjoint.integral_scalar_green h hh hK μ hμ hκv hψ hcψ).2.2
    _ = -(1 / 2 : ℝ) * ∫ x, scalarGradientPair h (fun y => κ y * v y) ψ x ∂μ := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun x => scalarGradientPair_symm h ψ (fun y => κ y * v y) x)
    _ = ∫ x, (κ x * v x) * laplacian h ψ x ∂μ :=
      (Adjoint.integral_scalar_green h hh hK μ hμ hψ hκv hcκv).2.2.symm
    _ = ∫ x, v x * laplacian h ψ x ∂μ := hright

theorem compactKahlerAdjoint {X : KahlerManifold n} (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ) :
    FlowMass.CompactKahlerAdjoint X h := by
  intro t ht μt hμt v ψ hv hψ hcψ
  exact compact_kahler_adjoint X.metric o (h t)
    (metricFamilySmooth_slice h (Set.Ici 0) hloc.1.2.1 t ht)
    (hloc.1.2.2.1 t ht) μt hμt v ψ hv hψ hcψ

theorem volumeAdjointTarget : FlowMass.VolumeAdjointTarget := by
  intro n X o h U P ρ hloc
  exact ⟨massVolumeTransport o h U P ρ hloc, riemannianVolumeLocality X,
    compactKahlerAdjoint o h U P ρ hloc⟩

end Yau.F04Proof
