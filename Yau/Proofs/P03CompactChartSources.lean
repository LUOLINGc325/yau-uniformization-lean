import Yau.Proofs.P03CompactPolynomialModels
import Yau.Proofs.P03TopPushforwardAE

open scoped Manifold Topology ContDiff
open Filter MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem oneFormPushforward_zero_of_model_zero (a x : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector r) (hF : F (chartPt a x) = 0) :
    oneFormPushforward (r := r) E a F x = (0 : NQForm E 1) x := by
  classical
  by_cases hx : x ∈ bundleChartSource (r := r) E a
  · change (if h : x ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a x h (F (chartPt a x)) else 0) = 0
    rw [dif_pos hx, hF, oneTensorFromCoefficients_zero]
  · change (if h : x ∈ bundleChartSource (r := r) E a then
      oneTensorFromCoefficients (r := r) E a x h (F (chartPt a x)) else 0) = 0
    exact dif_neg hx

theorem polynomial_chart_source_eventually_zero (a : M.Carrier)
    (F : ComplexVector n → ComplexVector r) (P : Fin r → MvPolynomial (Fin n) ℂ)
    (hF : F =ᶠ[𝓝 (chartPt a a)] (fun z => WithLp.toLp 2
      (fun α => MvPolynomial.eval (fun i => z i - chartPt a a i) (P α)))) :
    ∀ᶠ x in 𝓝 a,
      oneFormPushforward (r := r) E a (modelTopDbar F) x = (0 : NQForm E 1) x := by
  have hd := polynomial_model_eventually_dbar_zero hF
  have hcp : Tendsto (chartPt a) (𝓝 a) (𝓝 (chartPt a a)) :=
    (continuousAt_extChartAt (I := ComplexModel n) a).tendsto
  have hz : ∀ᶠ x in 𝓝 a, modelTopDbar F (chartPt a x) = 0 :=
    hcp.eventually hd
  filter_upwards [hz] with x hx
  exact oneFormPushforward_zero_of_model_zero E a x (modelTopDbar F) hx

theorem smooth_compact_chart_source (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (F : ComplexVector n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    SmoothForm (r := r) E (topFormPushforward (r := r) E a F) ∧
      SmoothForm (r := r) E (oneFormPushforward (r := r) E a (modelTopDbar F)) ∧
      WeakDbar (r := r) E (topFormPushforward (r := r) E a F)
        (oneFormPushforward (r := r) E a (modelTopDbar F)) ∧
      WeaklyClosed (r := r) E (oneFormPushforward (r := r) E a (modelTopDbar F)) ∧
      IsCompact (closure {x | oneFormPushforward (r := r) E a (modelTopDbar F) x ≠
        (0 : NQForm E 1) x}) := by
  have hu := topFormPushforward_smooth E hE a F hF hc hs
  have hD := topFormPushforward_isDbarOf E hE a F hF hc hs
  have hf := smoothForm_of_isDbarOf E _ _ hu hD
  have hw := weakDbar_of_smooth_isDbarOf E _ _ hu hf hD
  have hcD : HasCompactSupport (modelTopDbar F) :=
    hc.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelTopDbar_subset F)
  have hsD := (tsupport_modelTopDbar_subset F).trans hs
  have hK : IsCompact (chartInv a '' tsupport (modelTopDbar F)) :=
    hcD.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hsD.trans Set.inter_subset_left))
  exact ⟨hu, hf, hw, weakDbar_weaklyClosed_top E _ _ hw,
    hK.of_isClosed_subset isClosed_closure (oneFormPushforward_support E a _ hcD hsD)⟩

end Yau.NodeProofs.P03Aux
