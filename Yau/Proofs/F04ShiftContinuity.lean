import Yau.Proofs.F04ShiftZeroLevel
import Yau.Proofs.F04ShiftPositiveDifferential
import Yau.Proofs.F04PositiveIndicatorLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- Strong continuity of shifted truncation uses only the actual L2 values
and actual L2 differentials of the varying smooth shifts. -/
theorem dirichletShiftPosPart_tendsto
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : ℕ → M.Carrier → ℝ) (hr : ∀ j, SmoothFn (r j)) (hr0 : ∀ j x, x ∈ O → 0 ≤ r j x)
    (hr2 : ∀ j, ScalarL2 (μ.restrict O) (r j))
    (hdr2 : ∀ j, L2RealForm g.form (μ.restrict O) (scalarExterior (r j)))
    (r₀ : M.Carrier → ℝ) (hr₀ : SmoothFn r₀) (hr₀0 : ∀ x ∈ O, 0 ≤ r₀ x)
    (hr₀2 : ScalarL2 (μ.restrict O) r₀)
    (hdr₀2 : L2RealForm g.form (μ.restrict O) (scalarExterior r₀))
    (u : ℕ → DirichletEnergy g μ hμ O) (u₀ : DirichletEnergy g μ hμ O)
    (hu : Tendsto u atTop (𝓝 u₀))
    (hRH : Tendsto (fun j => scalarToLp (hr2 j)) atTop (𝓝 (scalarToLp hr₀2)))
    (hRD : Tendsto (fun j => realizeL2Form g (μ.restrict O)
      (L2FormSpace.ofSection (scalarExterior (r j)) (hdr2 j))) atTop
      (𝓝 (realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r₀) hdr₀2)))) :
    Tendsto (fun j => dirichletShiftPosPart g μ hμ O hO (r j) (hr j) (hr0 j) (hr2 j) (hdr2 j) (u j))
      atTop (𝓝 (dirichletShiftPosPart g μ hμ O hO r₀ hr₀ hr₀0 hr₀2 hdr₀2 u₀)) := by
  have hJsrc := ((dirichletL2 g μ hμ O).continuous.tendsto u₀).comp hu
  have hDsrc := ((dirichletD g μ hμ O).continuous.tendsto u₀).comp hu
  have hJ := hJsrc.sub hRH
  have hD := hDsrc.sub hRD
  have hJj (j : ℕ) := (dirichletShiftPosPart_spec g μ hμ O hO (r j) (hr j) (hr0 j) (hr2 j) (hdr2 j) (u j)).1
  have hDj (j : ℕ) := (dirichletShiftPosPart_spec g μ hμ O hO (r j) (hr j) (hr0 j) (hr2 j) (hdr2 j) (u j)).2
  have hSpec₀ := dirichletShiftPosPart_spec g μ hμ O hO r₀ hr₀ hr₀0 hr₀2 hdr₀2 u₀
  apply dirichlet_tendsto_of_graph_tendsto g μ hμ O
  · rw [hSpec₀.1]
    simpa only [Function.comp_def, hJj] using
      (Lp.continuous_posPart.tendsto (dirichletL2 g μ hμ O u₀ - scalarToLp hr₀2)).comp hJ
  · obtain ⟨A, hA, hrep⟩ := l2FormHilbert_exists_section g (μ.restrict O) (dirichletD g μ hμ O u₀)
    have hAd : L2RealForm g.form (μ.restrict O) (A - scalarExterior r₀) :=
      (l2FormSubmodule g (μ.restrict O) 1).sub_mem hA hdr₀2
    have hAdrep : realizeL2Form g (μ.restrict O)
        (L2FormSpace.ofSection (A - scalarExterior r₀) hAd) =
        dirichletD g μ hμ O u₀ -
          realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r₀) hdr₀2) := by
      rw [realize_section_sub g (μ.restrict O) A (scalarExterior r₀) hA hdr₀2 hAd, hrep]
    have hz := dirichlet_differential_eq_smooth_on_level g hK μ hμ O hO r₀ hr₀ u₀ A hA hrep.symm
    have hzero : ∀ᵐ x ∂μ.restrict O,
        (dirichletL2 g μ hμ O u₀ - scalarToLp hr₀2) x = 0 → (A - scalarExterior r₀) x = 0 := by
      filter_upwards [hz, Lp.coeFn_sub (dirichletL2 g μ hμ O u₀) (scalarToLp hr₀2),
        scalarToLp_coe hr₀2] with x hx hs hrx
      intro hf
      have hlevel : dirichletL2 g μ hμ O u₀ x = r₀ x := by
        apply sub_eq_zero.mp
        simpa only [hs, Pi.sub_apply, hrx] using hf
      change A x - scalarExterior r₀ x = 0
      rw [hx hlevel, sub_self]
    have hm := positiveFormMultiplier_tendsto_on_zero_level g (μ.restrict O)
      (fun j => dirichletL2 g μ hμ O (u j) - scalarToLp (hr2 j))
      (dirichletL2 g μ hμ O u₀ - scalarToLp hr₀2) (by simpa only [Function.comp_def] using hJ)
      (A - scalarExterior r₀) hAd hzero
      (fun j => dirichletD g μ hμ O (u j) - realizeL2Form g (μ.restrict O)
        (L2FormSpace.ofSection (scalarExterior (r j)) (hdr2 j)))
      (by simpa only [Function.comp_def, hAdrep] using hD)
    rw [hSpec₀.2]
    simpa only [hDj, hAdrep] using hm

theorem continuous_dirichletShiftPosPart
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r)) :
    Continuous (dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2) := by
  apply continuous_iff_seqContinuous.mpr
  intro seq u hu
  exact dirichletShiftPosPart_tendsto g hK μ hμ O hO (fun _ => r) (fun _ => hr)
    (fun _ => hr0) (fun _ => hr2) (fun _ => hdr2) r hr hr0 hr2 hdr2 seq u hu
    tendsto_const_nhds tendsto_const_nhds

end Yau.F04Proof
