import Yau.Proofs.F03DirichletClosure
import Yau.Proofs.F03ScalarL2Pairing

/-! The actual supported-energy resolvent and its variational graph. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
open LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

def dirichletClosedEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (u v : DirichletEnergy g μ hμ O) : ℝ :=
  ⟪u, v⟫_ℝ - ⟪dirichletL2 g μ hμ O u, dirichletL2 g μ hμ O v⟫_ℝ

theorem dirichletClosedEnergy_eq_differential (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (u v : DirichletEnergy g μ hμ O) :
    dirichletClosedEnergy g μ hμ O u v =
      (1 / 2 : ℝ) * ⟪dirichletD g μ hμ O u, dirichletD g μ hμ O v⟫_ℝ := by
  unfold dirichletClosedEnergy
  rw [dirichletEnergy_inner]
  ring

def dirichletResolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 (μ.restrict O) :=
  (dirichletL2 g μ hμ O).comp (dirichletL2 g μ hμ O).adjoint

theorem dirichlet_variational_iff_resolvent (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f w : Lp ℝ 2 (μ.restrict O)) :
    (∃ u : DirichletEnergy g μ hμ O, dirichletL2 g μ hμ O u = f ∧
      ∀ v, dirichletClosedEnergy g μ hμ O u v = ⟪w, dirichletL2 g μ hμ O v⟫_ℝ) ↔
      f = dirichletResolvent g μ hμ O (f + w) := by
  let J := dirichletL2 g μ hμ O
  constructor
  · rintro ⟨u, hu, he⟩
    have hau : u = J.adjoint (f + w) := by
      apply ext_inner_right ℝ
      intro v
      rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left]
      have h := he v
      unfold dirichletClosedEnergy at h
      rw [hu] at h
      linarith only [h]
    change f = J (J.adjoint (f + w))
    rw [← hau]
    exact hu.symm
  · intro hf
    refine ⟨J.adjoint (f + w), hf.symm, ?_⟩
    intro v
    change ⟪J.adjoint (f + w), v⟫_ℝ -
      ⟪J (J.adjoint (f + w)), J v⟫_ℝ = ⟪w, J v⟫_ℝ
    rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left]
    change f = J (J.adjoint (f + w)) at hf
    rw [← hf]
    ring

theorem dirichletResolvent_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    (dirichletResolvent g μ hμ O).adjoint = dirichletResolvent g μ hμ O := by
  rw [dirichletResolvent, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem dirichletResolvent_inner_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : Lp ℝ 2 (μ.restrict O)) :
    0 ≤ ⟪dirichletResolvent g μ hμ O f, f⟫_ℝ := by
  change 0 ≤ ⟪dirichletL2 g μ hμ O ((dirichletL2 g μ hμ O).adjoint f), f⟫_ℝ
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_self_nonneg

end Yau.Proofs.F03Aux
