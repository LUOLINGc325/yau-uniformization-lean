import Yau.Proofs.P06LocalCauchyLimitJets

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.LocalCauchyLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]

/-- A supplied pointwise limit is the very same smooth limit reconstructed
from the Cauchy sequence of actual full jets. -/
theorem smooth_fullJet_of_pointwise {f : ℕ → E → ℝ} {g : E → ℝ} {S : Set E}
    (hS : IsOpen S) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) S) (hc : FullJetCauchyOn f S)
    (hpoint : ∀ x ∈ S, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ ∞ g S ∧
      ∀ m (K : Set E), IsCompact K → K ⊆ S →
        TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (f j))
          (iteratedFDeriv ℝ m g) atTop K := by
  obtain ⟨v,hv,hlim⟩ := exists_smooth_fullJet_limit hS hf hc
  have he (x : E) (hx : x ∈ S) : v x = g x := by
    have h := (hlim 0 {x} isCompact_singleton (by simpa using hx)).tendsto_at (mem_singleton x)
    have h' := ((continuousMultilinearCurryFin0 ℝ E ℝ).continuous.tendsto
      (iteratedFDeriv ℝ 0 v x)).comp h
    have hvp : Tendsto (fun j => f j x) atTop (𝓝 (v x)) := by
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,
        LinearIsometryEquiv.apply_symm_apply] using h'
    exact tendsto_nhds_unique hvp (hpoint x hx)
  refine ⟨hv.congr (fun x hx => (he x hx).symm),?_⟩
  intro m K hK hKS
  apply (hlim m K hK hKS).congr_right
  intro x hx
  have hnear : v =ᶠ[𝓝 x] g :=
    Filter.eventually_of_mem (hS.mem_nhds (hKS hx)) fun y hy => he y hy
  exact (hnear.iteratedFDeriv ℝ m).self_of_nhds

theorem uniform_fullJet_difference {f : ℕ → E → ℝ} {g : E → ℝ} {S K : Set E}
    (hS : IsOpen S) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) S)
    (hg : ContDiffOn ℝ ∞ g S) (hKS : K ⊆ S) (m : ℕ)
    (hlim : TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (f j))
      (iteratedFDeriv ℝ m g) atTop K) (η : ℝ) (hη : 0 < η) :
    ∃ N, ∀ j, N ≤ j → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (fun q => f j q - g q) p‖ < η := by
  have h := Metric.tendstoUniformlyOn_iff.mp hlim η hη
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨N,fun j hj p hp => ?_⟩
  have hb := hN j hj p hp
  rw [dist_eq_norm,norm_sub_rev] at hb
  change ‖iteratedFDeriv ℝ m (f j-g) p‖ < η
  rw [iteratedFDeriv_sub_apply (i := m)
    (((hf j).contDiffAt (hS.mem_nhds (hKS hp))).of_le (by simp))
    ((hg.contDiffAt (hS.mem_nhds (hKS hp))).of_le (by simp))]
  exact hb

end Yau.NodeProofs.P06Aux.LocalCauchyLimit
