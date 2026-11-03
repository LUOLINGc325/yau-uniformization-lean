import Yau.Proofs.F04VariationalOrder

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.MassTargetStatements

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

/-- Nonnegative actual sources produce nonnegative original continuous weak
 traces. The zero solution and the order theorem are both proved internally. -/
theorem variationalSolution_nonnegative
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (h : ℝ → HermitianField M) {T C α shift : ℝ} (hT : 0 < T)
    (B : ℝ → DirichletEnergy g μ hμ O →L[ℝ] EnergyDual (DirichletEnergy g μ hμ O))
    (hForm : IntrinsicFormBinding g.form μ O h T C α shift
      (dirichletL2 g μ hμ O) (energyRepresentative g μ hμ O) B)
    (f : ℝ → FixedPivot μ O) (U : ℝ → DirichletEnergy g μ hμ O)
    (R : ℝ → EnergyDual (DirichletEnergy g μ hμ O)) (a : ℝ → FixedPivot μ O)
    (hSol : VariationalSolution μ O T (dirichletL2 g μ hμ O) B f U R a)
    (hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O, 0 ≤ f t x) :
    ∀ t ∈ Icc 0 T, ∀ᵐ x ∂μ.restrict O, 0 ≤ a t x := by
  have hZero : VariationalSolution μ O T (dirichletL2 g μ hμ O) B
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
    have hR0 := hSol.2.1.sub hSol.2.1
    refine ⟨MemLp.zero', ?_, continuousOn_const, rfl, ?_, ?_, ?_⟩
    · convert hR0 using 1
      funext t
      simp only [Pi.sub_apply, sub_self]
    · exact ae_of_all _ (fun _ => by simp)
    · intro v η _hη _hcη _hsη
      simp
    · exact ae_of_all _ (fun _ => by intro v; simp)
  have hOrder : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O, (0 : FixedPivot μ O) x ≤ f t x := by
    filter_upwards [hSrc] with t ht
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict O), ht] with x hx hfx
    rw [hx]
    exact hfx
  have hc := variationalSolution_order g hK μ hμ O hO h hT B hForm
    (fun _ => 0) f (fun _ => 0) U (fun _ => 0) R (fun _ => 0) a hZero hSol hOrder
  intro t ht
  filter_upwards [hc t ht, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict O)] with x hx hz
  rw [hz] at hx
  exact hx

end Yau.F04Proof
