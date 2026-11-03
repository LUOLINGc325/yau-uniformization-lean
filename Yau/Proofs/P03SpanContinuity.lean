import Yau.Proofs.P03SpanParameters
import Yau.Proofs.P03DeterminantFibres

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

theorem span_top_iff_linearEquiv_image {A B I : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (e : A ≃ₗ[ℂ] B) (v : I → A) :
    Submodule.span ℂ (range fun i => e (v i)) = ⊤ ↔
      Submodule.span ℂ (range v) = ⊤ := by
  rw [range_comp', Submodule.span_image_linearEquiv]
  exact Submodule.map_eq_top_iff

theorem span_top_iff_tangentCoords {n m : ℕ} {M : ComplexManifold n}
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source)
    (V : Fin m → TangentVector M x) :
    Submodule.span ℂ (range fun i => tangentCoords a x (V i)) = ⊤ ↔
      Submodule.span ℂ (range V) = ⊤ :=
  span_top_iff_linearEquiv_image (chartFrameEquiv a x hx).symm.toLinearEquiv V

theorem annihilatorEvaluationCLM_continuous {A : Type*} [TopologicalSpace A]
    {n m : ℕ} (V : A → Fin m → ComplexVector n) (hV : ∀ j, Continuous (fun x => V x j)) :
    Continuous (fun x => annihilatorEvaluationCLM (V x)) := by
  apply continuous_clm_apply.mpr
  intro q
  apply continuous_pi
  intro j
  have hc := (coordinatePairing q).continuous.comp (hV j)
  exact hc.congr (fun x => (annihilatorEvaluationCLM_apply (V x) q j).symm)

theorem annihilatorEvaluationCLM_continuousOn {A : Type*} [TopologicalSpace A]
    {n m : ℕ} (V : A → Fin m → ComplexVector n) {U : Set A}
    (hV : ∀ j, ContinuousOn (fun x => V x j) U) :
    ContinuousOn (fun x => annihilatorEvaluationCLM (V x)) U := by
  apply continuousOn_clm_apply.mpr
  intro q
  apply continuousOn_pi.mpr
  intro j
  have hc := (coordinatePairing q).continuous.comp_continuousOn (hV j)
  exact hc.congr (fun x _ => annihilatorEvaluationCLM_apply (V x) q j)

theorem isOpen_finite_span_top {A : Type*} [TopologicalSpace A] {n m : ℕ}
    (V : A → Fin m → ComplexVector n) (hV : ∀ j, Continuous (fun x => V x j)) :
    IsOpen {x | Submodule.span ℂ (range (V x)) = ⊤} := by
  have hc := ContinuousLinearMap.isOpen_injective.preimage
    (annihilatorEvaluationCLM_continuous V hV)
  convert hc using 1
  ext x
  exact span_top_iff_annihilatorEvaluation_injective (V x)

theorem isOpen_finite_span_top_inter {A : Type*} [TopologicalSpace A] {n m : ℕ}
    (V : A → Fin m → ComplexVector n) {U : Set A} (hU : IsOpen U)
    (hV : ∀ j, ContinuousOn (fun x => V x j) U) :
    IsOpen (U ∩ {x | Submodule.span ℂ (range (V x)) = ⊤}) := by
  have hc := (annihilatorEvaluationCLM_continuousOn V hV).isOpen_inter_preimage
    hU ContinuousLinearMap.isOpen_injective
  convert hc using 1
  ext x
  exact and_congr_right (fun _ => span_top_iff_annihilatorEvaluation_injective (V x))

end Yau.NodeProofs.P03Aux
