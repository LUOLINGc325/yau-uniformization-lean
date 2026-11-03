import Yau.Proofs.F03DirichletResolventBounds
import Yau.LeafProofs.L19HeatFamilyComplexification

/-! Complexification of the actual supported resolvent in the same restricted L² space. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def dirichletComplexResolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O) :=
  heatComplexify (μ.restrict O) (dirichletResolvent g μ hμ O)

theorem dirichletComplexResolvent_positive (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    (dirichletComplexResolvent g μ hμ O).IsPositive := by
  refine ⟨heatComplexify_isSymmetric (μ.restrict O) _ ?_, ?_⟩
  · exact (ContinuousLinearMap.eq_adjoint_iff _ _).mp
      (dirichletResolvent_adjoint g μ hμ O).symm
  · exact heatComplexify_re_inner_nonneg (μ.restrict O) _
      (dirichletResolvent_inner_nonneg g μ hμ O)

theorem dirichletComplexResolvent_selfAdjoint (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    IsSelfAdjoint (dirichletComplexResolvent g μ hμ O) :=
  (dirichletComplexResolvent_positive g μ hμ O).isSelfAdjoint

theorem dirichletComplexResolvent_norm_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : Lp ℂ 2 (μ.restrict O)) : ‖dirichletComplexResolvent g μ hμ O f‖ ≤ ‖f‖ :=
  heatComplexify_norm_le (μ.restrict O) _ (dirichletResolvent_norm_le g μ hμ O) f

theorem dirichletComplexResolvent_opNorm_le (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    ‖dirichletComplexResolvent g μ hμ O‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using dirichletComplexResolvent_norm_le g μ hμ O f

theorem dirichletComplexResolvent_injective (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (hO : IsOpen O) : Function.Injective (dirichletComplexResolvent g μ hμ O) :=
  heatComplexify_injective (μ.restrict O) _ (dirichletResolvent_injective g μ hμ O hO)

theorem dirichletComplexResolvent_denseRange (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (hO : IsOpen O) : DenseRange (dirichletComplexResolvent g μ hμ O) := by
  have hk : (dirichletComplexResolvent g μ hμ O).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (dirichletComplexResolvent_injective g μ hμ O hO)
  have heq := (dirichletComplexResolvent g μ hμ O).orthogonal_ker
  have hs : (dirichletComplexResolvent g μ hμ O).adjoint = dirichletComplexResolvent g μ hμ O :=
    (dirichletComplexResolvent_selfAdjoint g μ hμ O).star_eq
  rw [hk, Submodule.bot_orthogonal_eq_top, hs] at heq
  intro f
  have hf : f ∈ (dirichletComplexResolvent g μ hμ O).range.topologicalClosure := by
    rw [← heq]
    trivial
  exact hf

theorem dirichletComplexResolvent_spectrum (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    spectrum ℝ (dirichletComplexResolvent g μ hμ O) ⊆ Set.Icc 0 1 := by
  intro s hs
  have hpos : 0 ≤ dirichletComplexResolvent g μ hμ O :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (dirichletComplexResolvent_positive g μ hμ O)
  refine ⟨spectrum_nonneg_of_nonneg hpos hs, ?_⟩
  have hn := spectrum.norm_le_norm_mul_of_mem hs
  have hI : ‖(1 : Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hmul := mul_le_mul (dirichletComplexResolvent_opNorm_le g μ hμ O) hI
    (norm_nonneg _) zero_le_one
  exact (le_abs_self s).trans (hn.trans (by simpa using hmul))

theorem dirichletComplexResolvent_ofReal (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : Lp ℝ 2 (μ.restrict O)) :
    dirichletComplexResolvent g μ hμ O (heatLpOfReal (μ.restrict O) f) =
      heatLpOfReal (μ.restrict O) (dirichletResolvent g μ hμ O f) :=
  heatComplexify_ofReal (μ.restrict O) _ f

end Yau.Proofs.F03Aux
