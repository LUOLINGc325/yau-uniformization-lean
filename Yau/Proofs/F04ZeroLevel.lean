import Yau.Proofs.F04PositiveDifferential
import Yau.Proofs.F04GraphDifferentialLinear

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichlet_pos_neg_decomposition (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (u : DirichletEnergy g μ hμ O) :
    u = dirichletPosPart g μ hμ O hO u - dirichletPosPart g μ hμ O hO (-u) := by
  apply dirichletL2_injective g hK μ hμ O hO
  rw [map_sub, (dirichletPosPart_spec g μ hμ O hO u).1,
    (dirichletPosPart_spec g μ hμ O hO (-u)).1, map_neg]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (Lp.posPart (dirichletL2 g μ hμ O u))
      (Lp.posPart (-dirichletL2 g μ hμ O u)),
    Lp.coeFn_posPart (dirichletL2 g μ hμ O u),
    Lp.coeFn_posPart (-dirichletL2 g μ hμ O u),
    Lp.coeFn_neg (dirichletL2 g μ hμ O u)] with x hs hp hn hm
  rw [hs]
  simp only [Pi.sub_apply, Pi.neg_apply, hp, hn, hm]
  rcases le_total 0 (dirichletL2 g μ hμ O u x) with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    ring

/-- Zero-level locality follows from the two strict active-set differential
formulas. No pointwise derivative of a rough L2 representative is asserted. -/
theorem dirichlet_differential_zero_on_zero_level (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (u : DirichletEnergy g μ hμ O)
    (A : RealForm M 1) (hA : L2RealForm g.form (μ.restrict O) A)
    (hDu : dirichletD g μ hμ O u =
      realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection A hA)) :
    ∀ᵐ x ∂μ.restrict O, dirichletL2 g μ hμ O u x = 0 → A x = 0 := by
  have hnegA : L2RealForm g.form (μ.restrict O) (-A) :=
    (l2FormSubmodule g (μ.restrict O) 1).neg_mem hA
  have hDneg : dirichletD g μ hμ O (-u) =
      realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (-A) hnegA) := by
    rw [map_neg, hDu, realize_section_neg]
  obtain ⟨hAp, hDp⟩ := dirichlet_posPart_differential g hK μ hμ O hO u A hA hDu
  obtain ⟨hAn, hDn⟩ := dirichlet_posPart_differential g hK μ hμ O hO (-u) (-A) hnegA hDneg
  let Ap : RealForm M 1 := fun x => if 0 < dirichletL2 g μ hμ O u x then A x else 0
  let An : RealForm M 1 := fun x => if 0 < dirichletL2 g μ hμ O (-u) x then (-A) x else 0
  have hsub : L2RealForm g.form (μ.restrict O) (Ap - An) :=
    (l2FormSubmodule g (μ.restrict O) 1).sub_mem hAp hAn
  have he : realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection A hA) =
      realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (Ap - An) hsub) := by
    rw [realize_section_sub g (μ.restrict O) Ap An hAp hAn hsub, ← hDp, ← hDn, ← map_sub,
      ← dirichlet_pos_neg_decomposition g hK μ hμ O hO u, ← hDu]
  have hae := (realizeL2Form_eq_iff_ae g (μ.restrict O) _ _).mp he
  have hneg : ∀ᵐ x ∂μ.restrict O,
      dirichletL2 g μ hμ O (-u) x = -(dirichletL2 g μ hμ O u x) := by
    filter_upwards [Lp.coeFn_neg (dirichletL2 g μ hμ O u)] with x hx
    simpa only [map_neg, Pi.neg_apply] using hx
  filter_upwards [hae, hneg] with x hx hn
  intro hz
  have hp0 : ¬0 < dirichletL2 g μ hμ O u x := by rw [hz]; exact lt_irrefl 0
  have hn0 : ¬0 < dirichletL2 g μ hμ O (-u) x := by rw [hn, hz, neg_zero]; exact lt_irrefl 0
  simpa only [L2FormSpace.toSection_ofSection, Pi.sub_apply, Ap, An,
    ite_eq_right hp0, ite_eq_right hn0, sub_self] using hx

end Yau.F04Proof
