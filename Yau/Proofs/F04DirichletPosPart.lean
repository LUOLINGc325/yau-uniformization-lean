import Yau.Proofs.F03DirichletPositivePart

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The positive part is chosen from the proved supported-energy closure,
with no prescription of its weak differential at this stage. -/
def dirichletPosPart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (u : DirichletEnergy g μ hμ O) : DirichletEnergy g μ hμ O :=
  Classical.choose (dirichletEnergy_posPart_L2 g μ hμ O hO u)

theorem dirichletPosPart_spec (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (u : DirichletEnergy g μ hμ O) :
    dirichletL2 g μ hμ O (dirichletPosPart g μ hμ O hO u) =
        Lp.posPart (dirichletL2 g μ hμ O u) ∧
      ‖dirichletPosPart g μ hμ O hO u‖ ^ 2 -
          ‖dirichletL2 g μ hμ O (dirichletPosPart g μ hμ O hO u)‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖dirichletL2 g μ hμ O u‖ ^ 2 :=
  Classical.choose_spec (dirichletEnergy_posPart_L2 g μ hμ O hO u)

theorem dirichletPosPart_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (u : DirichletEnergy g μ hμ O) : ‖dirichletPosPart g μ hμ O hO u‖ ≤ ‖u‖ := by
  have hs := dirichletPosPart_spec g μ hμ O hO u
  have hn : ‖Lp.posPart (dirichletL2 g μ hμ O u)‖ ≤ ‖dirichletL2 g μ hμ O u‖ := by
    simpa only [Lp.posPart, NNReal.coe_one, one_mul] using
      Lp.lipschitzWith_pos_part.norm_compLp_le (max_eq_right (le_refl (0 : ℝ)))
        (dirichletL2 g μ hμ O u)
  rw [hs.1] at hs
  nlinarith [norm_nonneg (dirichletPosPart g μ hμ O hO u), norm_nonneg u,
    norm_nonneg (Lp.posPart (dirichletL2 g μ hμ O u)), norm_nonneg (dirichletL2 g μ hμ O u)]

theorem dirichletPosPart_unique (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    (u v : DirichletEnergy g μ hμ O)
    (hv : dirichletL2 g μ hμ O v = Lp.posPart (dirichletL2 g μ hμ O u)) :
    dirichletPosPart g μ hμ O hO u = v := by
  apply dirichletL2_injective g hK μ hμ O hO
  exact (dirichletPosPart_spec g μ hμ O hO u).1.trans hv.symm

end Yau.F04Proof
