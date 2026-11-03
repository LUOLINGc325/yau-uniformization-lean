import Yau.Proofs.F04ShiftPositiveGraph

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- Exact shifted active-set differential with any actual representative of
Du. Only nonnegativity on the actual open domain is required of the shift. -/
theorem dirichlet_shift_posPart_differential
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) (A : RealForm M 1)
    (hA : L2RealForm g.form (μ.restrict O) A)
    (hDu : dirichletD g μ hμ O u = realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection A hA)) :
    ∃ hB : L2RealForm g.form (μ.restrict O)
      (fun x => if r x < dirichletL2 g μ hμ O u x then A x - scalarExterior r x else 0),
      dirichletD g μ hμ O (dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u) =
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection
          (fun x => if r x < dirichletL2 g μ hμ O u x then A x - scalarExterior r x else 0) hB) := by
  have hAd : L2RealForm g.form (μ.restrict O) (A - scalarExterior r) :=
    (l2FormSubmodule g (μ.restrict O) 1).sub_mem hA hdr2
  let f := dirichletL2 g μ hμ O u - scalarToLp hr2
  let B : RealForm M 1 := fun x => if 0 < f x then (A - scalarExterior r) x else 0
  let C : RealForm M 1 := fun x =>
    if r x < dirichletL2 g μ hμ O u x then A x - scalarExterior r x else 0
  have hB : L2RealForm g.form (μ.restrict O) B := positive_active_form_l2 g (μ.restrict O) f _ hAd
  have hBC : ∀ᵐ x ∂μ.restrict O, B x = C x := by
    filter_upwards [Lp.coeFn_sub (dirichletL2 g μ hμ O u) (scalarToLp hr2), scalarToLp_coe hr2]
      with x hx hrx
    simp only [B, C, f, hx, Pi.sub_apply, hrx, sub_pos]
  have hC := l2RealForm_of_ae_eq g.form hBC hB
  refine ⟨hC, ?_⟩
  have hDR : dirichletD g μ hμ O u -
      realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2) =
      realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (A - scalarExterior r) hAd) := by
    rw [hDu, realize_section_sub]
  rw [(dirichletShiftPosPart_spec g μ hμ O hO r hr hr0 hr2 hdr2 u).2, hDR,
    positiveFormMultiplier_realize]
  exact (realizeL2Form_eq_iff_ae g (μ.restrict O) _ _).mpr hBC

/-- Literal supported shifted graph output, with L2 membership of its actual
active differential produced internally. -/
theorem dirichlet_shift_posPart_graph
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) (A : RealForm M 1)
    (hA : L2RealForm g.form (μ.restrict O) A)
    (hDu : dirichletD g μ hμ O u = realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection A hA)) :
    ∃ v : DirichletEnergy g μ hμ O,
      ∃ hB : L2RealForm g.form (μ.restrict O)
        (fun x => if r x < dirichletL2 g μ hμ O u x then A x - scalarExterior r x else 0),
      dirichletL2 g μ hμ O v = Lp.posPart (dirichletL2 g μ hμ O u - scalarToLp hr2) ∧
        dirichletD g μ hμ O v = realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection
          (fun x => if r x < dirichletL2 g μ hμ O u x then A x - scalarExterior r x else 0) hB) := by
  obtain ⟨hB, hD⟩ := dirichlet_shift_posPart_differential g μ hμ O hO r hr hr0 hr2 hdr2 u A hA hDu
  exact ⟨dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u, hB,
    (dirichletShiftPosPart_spec g μ hμ O hO r hr hr0 hr2 hdr2 u).1, hD⟩

end Yau.F04Proof
