import Yau.Proofs.P06ContinuousHeat
import Yau.Proofs.G02GluedVolume

noncomputable section
open MeasureTheory
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

/-- The continuous-initial class has the expected genuine constant solution. -/
theorem continuousInitialHeat_constant (g : HermitianField M) (c : ℝ) :
    IsContinuousInitialScalarHeat g (fun _ => c) (fun _ _ => c) := by
  refine ⟨fun _ => rfl, (fun _ => contDiffOn_const), ?_, ?_, ?_⟩
  · intro x t _ht
    rw [Yau.LeafProofs.L18Aux.laplacian_const]
    exact hasDerivAt_const t c
  · intro T _hT
    exact ⟨|c|, abs_nonneg c, fun _ _ _ _ => le_rfl⟩
  · intro K _hK ε hε
    exact ⟨1, zero_lt_one, fun _ _ _ _ _ => by simpa only [sub_self, abs_zero] using hε.le⟩

/-- A direct empty-index check of the original Hessian conclusion in complex
dimension zero.  It uses the computed matrices, with no geometry premise. -/
theorem hessianBound_dimZero {M : ComplexManifold 0} (g : HermitianField M)
    (f : M.Carrier → ℝ) (C : ℝ) (x : M.Carrier) :
    HermLE (levi f x) ((C : ℂ) • gMat g x) := by
  change (((C : ℂ) • gMat g x - levi f x) : Matrix (Fin 0) (Fin 0) ℂ).PosSemidef
  have hzero : ((C : ℂ) • gMat g x - levi f x) = 0 := Subsingleton.elim _ _
  rw [hzero]
  exact Matrix.PosSemidef.zero

end Yau.NodeProofs.P06Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint

/-- The existence projection of the original P06 rough scalar clause, with
no additional premise or supplied heat evolution. -/
theorem P06_rough_existence_proved :
    ∀ (n : ℕ) (X : KahlerManifold n) (f : Pt X → ℝ),
      LipschitzForMetric X.metric.form f → ConstantOutsideCompact f →
        ∃ u, IsContinuousInitialScalarHeat X.metric.form f u := by
  intro n X f hf hcf
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  exact P06Aux.continuousInitialHeat_exists
    (Yau.LeafProofs.L12Aux.complexDimension_pos X.manifold) X.metric X.kahler_metric μ hμ f hf hcf

end Yau.NodeProofs
