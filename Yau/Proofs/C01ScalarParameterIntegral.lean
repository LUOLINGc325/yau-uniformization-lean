import Yau.Proofs.C01ParameterIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The actual scalar derivative of a compact parameter integral is
its integral derivative. Pointwise derivatives are checked against the
genuine Fréchet derivative before commuting evaluation and integration. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

theorem scalar_unitIntegral_hasDerivAt
    (F : ℝ × ℝ → ℝ) (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) (hF : ContDiffOn ℝ 1 F (I ×ˢ J))
    (a : ℝ) (ha : a ∈ I) (D : ℝ → ℝ)
    (hD : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => F (t, u)) (D u) a) :
    HasDerivAt (fun t => ∫ u in Set.Icc (0 : ℝ) 1, F (t, u))
      (∫ u in Set.Icc (0 : ℝ) 1, D u) a := by
  have Hp := Parametric.hasFDerivAt_unitIntegral hI hJ hunit hF ha
  have hDc : ContinuousOn (Parametric.parameterDerivative F) (I ×ˢ J) :=
    (Parametric.parameterDerivative_contDiffOn hI hJ 0 (by simpa using hF)).continuousOn
  have hslice : ContinuousOn (fun u => Parametric.parameterDerivative F (a, u)) (Set.Icc (0 : ℝ) 1) :=
    hDc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨ha, hunit hu⟩)
  have hDi : IntegrableOn (fun u => Parametric.parameterDerivative F (a, u))
      (Set.Icc (0 : ℝ) 1) volume := hslice.integrableOn_compact isCompact_Icc
  have hcoef (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      Parametric.parameterDerivative F (a, u) 1 = D u := by
    have hFD : DifferentiableAt ℝ F (a, u) :=
      (hF.contDiffAt ((hI.prod hJ).mem_nhds ⟨ha, hunit hu⟩)).differentiableAt_one
    exact (Parametric.parameterDerivative_hasFDerivAt F hFD).hasDerivAt.unique (hD u hu)
  have HD := Hp.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hDi 1] at HD
  have hEq : (∫ u in Set.Icc (0 : ℝ) 1, Parametric.parameterDerivative F (a, u) 1) =
      ∫ u in Set.Icc (0 : ℝ) 1, D u := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hcoef u hu
  rw [hEq] at HD
  exact HD

end Yau.NodeProofs.C01Aux
