import Yau.Proofs.F04FlowMassDerivative
import Yau.Proofs.F04DensityAdjoint

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

theorem c1_timeDerivative_slice_continuous {n : ℕ} {M : ComplexManifold n}
    {I : Set ℝ} (hI : IsOpen I) {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v I)
    {t : ℝ} (ht : t ∈ I) : Continuous (fun x => deriv (v x) t) := by
  have hc := smoothSpaceC1Time_timeDerivative_continuousOn hI hv
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hc.continuousAt ((isOpen_univ.prod hI).mem_nhds ⟨mem_univ _, ht⟩)).comp
    (continuous_id.prodMk continuous_const).continuousAt

theorem flow_scalarCurvature_slice_continuous {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 < t) : Continuous (scalarCurvature (h t)) := by
  have hsub : Ioi (0 : ℝ) ⊆ Ici (0 : ℝ) := Set.Ioi_subset_Ici_self
  have hρ : SmoothSpaceC1Time ρ (Ioi 0) :=
    smoothSpaceTime_c1 (M := X.manifold) (I := Ioi (0 : ℝ)) (v := ρ)
      (fun x => (hloc.2.2.2.1 x).mono
        (Set.prod_mono (Subset.refl _) hsub))
  have hc := c1_timeDerivative_slice_continuous isOpen_Ioi hρ ht
  have heq : (fun x => deriv (ρ x) t) = scalarCurvature (h t) := by
    funext x
    exact ((rho_hasDerivWithinAt o h U P ρ hloc x t ht.le).hasDerivAt (Ici_mem_nhds ht)).deriv
  rw [heq] at hc
  exact hc

theorem laplacian_compact_support {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) {ψ : M.Carrier → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (laplacian h ψ) := by
  apply HasCompactSupport.of_support_subset_isCompact hψ
  intro x hx
  by_contra hh
  exact hx (laplacian_zero_of_notMem_tsupport h ψ hh)

theorem initial_volume_integrable_of_continuous_compact {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v : M.Carrier → ℝ} (hv : Continuous v) (hc : HasCompactSupport v) : Integrable v μ := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  exact hv.integrable_of_hasCompactSupport hc

end Yau.F04Proof
