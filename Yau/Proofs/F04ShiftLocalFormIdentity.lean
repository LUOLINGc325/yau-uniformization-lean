import Yau.Proofs.F04ShiftFormIdentity

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- The shifted energy identity uses the genuine small-domain Laplacian.
 Its L2 membership is derived from the actual matching compact profile. -/
theorem localCoreForm_shift_identity_local
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {O W : Set M.Carrier}
    (hO : IsOpen O) (hW : IsOpen W) (hOW : O ⊆ W)
    (H : HermitianField M) (hH : MetricSmooth H)
    (B : DirichletEnergy g μ hμ O →L[ℝ] DirichletEnergy g μ hμ O →L[ℝ] ℝ)
    (A : DirichletEnergy g μ hμ W →L[ℝ] DirichletEnergy g μ hμ W →L[ℝ] ℝ)
    (hB : ∀ f v : dirichletCore g μ hμ O,
      B (dirichletCoreToEnergy g μ hμ O f) (dirichletCoreToEnergy g μ hμ O v) =
        -(∫ x in O, v.val x * laplacian H f.val x ∂μ))
    (hA : ∀ f v : dirichletCore g μ hμ W,
      A (dirichletCoreToEnergy g μ hμ W f) (dirichletCoreToEnergy g μ hμ W v) =
        -(∫ x in W, v.val x * laplacian H f.val x ∂μ))
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (f : dirichletCore g μ hμ W) (hf0 : ∀ x ∈ W, 0 ≤ f.val x)
    (hfr : ∀ x ∈ O, f.val x = r x) (u : DirichletEnergy g μ hμ O) :
    let w := dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u
    ∃ hL : ScalarL2 (μ.restrict O) (laplacian H r),
      B u w + inner ℝ (scalarToLp hL) (dirichletL2 g μ hμ O w) =
        A (dirichletInclusion g μ hμ hOW w) (dirichletInclusion g μ hμ hOW w) := by
  let w := dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u
  have hEq : laplacian H f.val =ᵐ[μ.restrict O] laplacian H r := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    have he : (f.val : M.Carrier → ℝ) =ᶠ[𝓝 x] r :=
      eventually_of_mem (hO.mem_nhds hx) (fun y hy => hfr y hy)
    exact laplacian_congr_of_eventuallyEq H he
  have hLF := dirichletCore_laplacian_scalarL2 g μ hμ W H hH f
  have hLp := ((scalarL2_iff_memLp _ _).mp hLF).mono_measure (Measure.restrict_mono hOW le_rfl)
  have hL : ScalarL2 (μ.restrict O) (laplacian H r) :=
    (scalarL2_iff_memLp _ _).mpr ((memLp_congr_ae hEq).mp hLp)
  have hPair := dirichletInclusion_L2_pairing g μ hμ hO.measurableSet hW.measurableSet hOW
    (laplacian H r) (laplacian H f.val) hL hLF hEq w
  have hid := localCoreForm_shift_identity g hK μ hμ hO hW hOW H hH B A hB hA
    r hr hr0 hr2 hdr2 f hf0 hfr u
  change B u w + inner ℝ (scalarToLp hLF)
    (dirichletL2 g μ hμ W (dirichletInclusion g μ hμ hOW w)) = _ at hid
  rw [hPair] at hid
  exact ⟨hL, hid⟩

end Yau.F04Proof
