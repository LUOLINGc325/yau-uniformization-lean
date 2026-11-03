import Yau.Proofs.F01ANativeGlobalKahlerCore

/-! The same core's actual logdet heat identity, including closed faces.
The scalar P is identified with the native quotient only where needed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem localizedFlowCore_logdet_heat_identity
    {X : KahlerManifold n} {h : Flow X} {U P ρ : STF X}
    (hc : LocalizedFlowCore X h U P ρ) {T : ℝ} (hT : 0 < T)
    (x : Pt X) {t : ℝ} (ht : t ∈ Icc 0 T) :
    fieldHeatWithin h (Icc 0 T) (fun s y => P y s) x t =
      -traceWith (gMat (h t) x) (ricci X.metric.form x) := by
  rcases hc with ⟨hKRF, _, _, _, _, _, _, _, hPlog, _, _⟩
  have hg := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ hs => hs.1
  have hmetric (i j : Fin n) := (hKRF.2.2.2 x t ht.1 i j).mono hsub
  have hNative := native_logdet_ratio_heat_identity X.metric.form hg h
    (metricFamilySmooth_slice hKRF.2.1 ht.1) x ((uniqueDiffOn_Icc hT) t ht) hmetric
  have hPeq : P x =ᶠ[𝓝[Icc 0 T] t] flowLogDetRatio X.metric.form h x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hPlog x s hs.1
  have hSpace : (fun y => P y t) = fun y => flowLogDetRatio X.metric.form h y t :=
    funext (fun y => hPlog y t ht.1)
  unfold fieldHeatWithin at hNative ⊢
  change derivWithin (P x) (Icc 0 T) t - laplacian (h t) (fun y => P y t) x = _
  rw [hPeq.derivWithin_eq_of_mem ht, hSpace]
  exact hNative

end Yau.NodeProofs.F01Aux
