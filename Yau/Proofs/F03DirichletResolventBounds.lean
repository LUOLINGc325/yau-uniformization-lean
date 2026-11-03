import Yau.Proofs.F03DirichletResolvent

/-! Contraction, injectivity and dense range of the supported resolvent. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

theorem dirichletL2_adjoint_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : Lp ℝ 2 (μ.restrict O)) : ‖(dirichletL2 g μ hμ O).adjoint f‖ ≤ ‖f‖ := by
  let J := dirichletL2 g μ hμ O
  have hi : ‖J.adjoint f‖ ^ 2 = ⟪f, J (J.adjoint f)⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left]
  have hb := dirichletL2_norm_le g μ hμ O (J.adjoint f)
  have hcs := real_inner_le_norm f (J (J.adjoint f))
  have hmul := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
  nlinarith [norm_nonneg (J.adjoint f), norm_nonneg f]

theorem dirichletResolvent_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : Lp ℝ 2 (μ.restrict O)) : ‖dirichletResolvent g μ hμ O f‖ ≤ ‖f‖ :=
  (dirichletL2_norm_le g μ hμ O _).trans (dirichletL2_adjoint_norm_le g μ hμ O f)

theorem dirichletResolvent_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    ‖dirichletResolvent g μ hμ O‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using dirichletResolvent_norm_le g μ hμ O f

theorem dirichletResolvent_injective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O) :
    Function.Injective (dirichletResolvent g μ hμ O) := by
  have hJ : Function.Injective (dirichletL2 g μ hμ O).adjoint := by
    intro f k hfk
    apply ext_inner_right ℝ
    intro v
    refine (dirichletL2_denseRange g μ hμ O hO).induction_on v
      (isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner continuous_id)) ?_
    intro w
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.adjoint_inner_left, hfk]
  exact (dirichletL2 g μ hμ O).self_comp_adjoint_injective_iff.mpr hJ

theorem dirichletResolvent_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O) :
    DenseRange (dirichletResolvent g μ hμ O) := by
  have hk : (dirichletResolvent g μ hμ O).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (dirichletResolvent_injective g μ hμ O hO)
  have heq := (dirichletResolvent g μ hμ O).orthogonal_ker
  rw [hk, Submodule.bot_orthogonal_eq_top, dirichletResolvent_adjoint] at heq
  intro f
  have hf : f ∈ (dirichletResolvent g μ hμ O).range.topologicalClosure := by
    rw [← heq]
    trivial
  exact hf

end Yau.Proofs.F03Aux
