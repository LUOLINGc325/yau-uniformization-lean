import Yau.Proofs.P03Measure

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

/-- Glue locally constructed representatives by open-positive uniqueness,
then use an actual countable subcover for the final AE assertion. -/
theorem glue_local_holomorphic_representatives
    {U : Set (ComplexVector n)} {u : ComplexVector n → ℂ}
    (r : U → ℝ) (hr : ∀ a, 0 < r a)
    (hKU : ∀ a : U, Metric.closedBall a.1 (4 * r a) ⊆ U)
    (g : U → ComplexVector n → ℂ) (hc : ∀ a, Continuous (g a))
    (hh : ∀ a : U, DifferentiableOn ℂ (g a) (Metric.ball a.1 (3 * r a)))
    (hae : ∀ a : U, u =ᵐ[(volume : Measure (ComplexVector n)).restrict
      (Metric.ball a.1 (2 * r a))] g a) :
    ∃ v : ComplexVector n → ℂ, DifferentiableOn ℂ v U ∧
      u =ᵐ[(volume : Measure (ComplexVector n)).restrict U] v := by
  classical
  let W : U → Set (ComplexVector n) := fun a => Metric.ball a.1 (2 * r a)
  have hsub (a : U) : W a ⊆ U := by
    intro x hx
    apply hKU a
    apply Metric.mem_closedBall.mpr
    have hd := Metric.mem_ball.mp hx
    have hp := hr a
    linarith
  have hself (a : U) : a.1 ∈ W a :=
    Metric.mem_ball_self (mul_pos (by norm_num) (hr a))
  have hcover : (⋃ a : U, W a) = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact hsub a ha
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hself ⟨x, hx⟩⟩
  have hcompat (a b : U) : Set.EqOn (g a) (g b) (W a ∩ W b) := by
    have ha : u =ᵐ[(volume : Measure (ComplexVector n)).restrict (W a ∩ W b)] g a :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hae a)
    have hb : u =ᵐ[(volume : Measure (ComplexVector n)).restrict (W a ∩ W b)] g b :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hae b)
    exact (volume : Measure (ComplexVector n)).eqOn_open_of_ae_eq (ha.symm.trans hb)
      (Metric.isOpen_ball.inter Metric.isOpen_ball) (hc a).continuousOn (hc b).continuousOn
  let v : ComplexVector n → ℂ := fun x => if hx : x ∈ U then g ⟨x, hx⟩ x else 0
  have hveq (a : U) : Set.EqOn v (g a) (W a) := by
    intro x hx
    have hxU := hsub a hx
    change (if h : x ∈ U then g ⟨x, h⟩ x else 0) = g a x
    rw [dif_pos hxU]
    exact hcompat ⟨x, hxU⟩ a ⟨hself ⟨x, hxU⟩, hx⟩
  refine ⟨v, ?_, ?_⟩
  · intro x hx
    let a : U := ⟨x, hx⟩
    have hxW : x ∈ W a := hself a
    have hEq : v =ᶠ[𝓝 x] g a :=
      (hveq a).eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hxW)
    have hx3 : x ∈ Metric.ball a.1 (3 * r a) :=
      Metric.mem_ball_self (mul_pos (by norm_num) (hr a))
    have hd := (hh a x hx3).differentiableAt (Metric.isOpen_ball.mem_nhds hx3)
    exact (hd.congr_of_eventuallyEq hEq).differentiableWithinAt
  · obtain ⟨T, hT, hTW⟩ := TopologicalSpace.isOpen_iUnion_countable W (fun _ => Metric.isOpen_ball)
    have hTU : (⋃ a ∈ T, W a) = U := hTW.trans hcover
    have hparts (a : U) (ha : a ∈ T) :
        u =ᵐ[(volume : Measure (ComplexVector n)).restrict (W a)] v := by
      have hv : g a =ᵐ[(volume : Measure (ComplexVector n)).restrict (W a)] v := by
        apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
        exact Filter.Eventually.of_forall fun x hx => (hveq a hx).symm
      exact (hae a).trans hv
    have h := (ae_eq_restrict_biUnion_iff W hT u v).mpr hparts
    simpa only [hTU] using h

end Yau.NodeProofs.P03Aux
