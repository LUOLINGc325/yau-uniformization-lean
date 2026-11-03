import Yau.Proofs.P06CompactDifferenceCurrent
import Yau.Proofs.P06ContinuousHeatHilbert
import Yau.Proofs.P06LeviConstantShift
import Yau.Proofs.P06SmoothCurrentSeparation

noncomputable section
open MeasureTheory
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ}

/-- The literal rough-PDE solution satisfies the original same-C pointwise
Levi bound. No Hessian or global L² assumption is imposed on that solution. -/
theorem continuousInitialHeat_hessian_upper (X : KahlerManifold n)
    (f : Pt X → ℝ) (C : ℝ) (hf : LipschitzForMetric X.metric.form f)
    (hc : ConstantOutsideCompact f) (hw : WeakLeviUpper X.metric.form f C)
    (u : ℝ → Pt X → ℝ) (hu : IsContinuousInitialScalarHeat X.metric.form f u)
    (t : ℝ) (ht : 0 < t) (x : Pt X) :
    HermLE (levi (u t) x) ((C : ℂ) • gMat X.metric.form x) := by
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  obtain ⟨c, hcont, hcompact⟩ := compactExterior_difference X.metric hf hc
  have hs : SmoothFn (fun y => u t y - c) := by
    have hslice := Yau.LeafProofs.L19Aux.smoothSpaceTime_slice hu.2.1 ht
    intro a
    exact (hslice a).sub contDiffOn_const
  obtain ⟨huL, _, huRep⟩ := continuousInitialHeat_normalized_hilbert X μ hμ
    f c hcont hcompact u hu t ht
  have hb := CurrentSeparation.smooth_levi_upper_of_compact_positive_tests X.metric μ hμ
    (fun y => u t y - c) hs C
    (fun B hB hcB h11 hp => compactDifferenceHeat_current_upper X μ hμ f C hf hc hw
      c hcont hcompact t ht (fun y => u t y - c) hs huL huRep B hB hcB h11 hp) x
  rwa [levi_sub_constant] at hb

end Yau.NodeProofs.P06Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint

/-- The full original Lipschitz Hessian heat target, including the actual
continuous-initial PDE class, uniqueness, and the same paper constant. -/
theorem P06_Lipschitz_Hessian_heat_proved :
    ∀ (n : ℕ) (X : KahlerManifold n), LipschitzHessianHeatTarget X := by
  intro n X f C hf hc hw
  refine ⟨P06_rough_existence_proved n X f hf hc, ?_, ?_⟩
  · intro u v hu hv t ht
    exact P06Aux.continuousInitialScalarHeat_unique X f u v hu hv t ht
  · intro u hu t ht x
    exact P06Aux.continuousInitialHeat_hessian_upper X f C hf hc hw u hu t ht x

end Yau.NodeProofs
