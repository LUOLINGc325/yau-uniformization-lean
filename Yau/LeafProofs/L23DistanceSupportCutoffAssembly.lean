import Yau.LeafProofs.L23JetBernsteinInduction
import Yau.LeafProofs.L23LocalDistanceSupportCutoff

/-! Genuine local distance-square upper supports supply exactly the preselected Bernstein cutoffs. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {n : ℕ} {M : ComplexManifold n}

theorem derivativeCutoffSupports_of_upperSupports
    (h : ℝ → HermitianField M) (p : M.Carrier) (a K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ)
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hBuild : ∀ (rIn rOut : ℝ), 0<rIn → rIn<rOut → rOut≤2*r →
      ∀ q∈distBall (h a) p rIn, ∀ (y : M.Carrier) (t : ℝ), t∈Set.Ioo a (a+2*τ) →
      inducedDistance (h t) q y<Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4 →
      ∃ E : M.Carrier → ℝ → ℝ,
        ContDiffAt ℝ 2 (fun z : ComplexVector n × ℝ => E (chartInv y z.1) z.2) (chartPt y y,t) ∧
        E y t=inducedDistance (h t) q y^2 ∧
        (∀ᶠ z in 𝓝 (y,t), inducedDistance (h z.2) q z.1^2≤E z.1 z.2) ∧
        realGradPair (h t) (fun z => E z t) (fun z => E z t) y=4*inducedDistance (h t) q y^2 ∧
        realLap (h t) (fun z => E z t) y≤
          2*(2*n : ℕ)+(2/3 : ℝ)*(2*n : ℕ)*K*inducedDistance (h t) q y^2 ∧
        -σ*(2*n : ℕ)*K*inducedDistance (h t) q y^2≤deriv (E y) t) :
    DerivativeCutoffSupports h p a K r τ σ := by
  intro k q hq b₀ T hab₀ hb₀T hT
  intro y hy t ht hηpos
  have htI : t∈Set.Ioo a (a+2*τ) := ⟨hab₀.trans_lt ht.1,ht.2.trans_lt hT⟩
  have hh := metricFamilySmooth_slice h hflow.1 ⟨htI.1.le,htI.2.le⟩
  have hR := derivativeCutoffRadius_pos n K r τ σ hr (k+1)
  have hshort := (timeDistanceCutoff_pos_iff h q y hR hh).mp hηpos
  have hshort' : inducedDistance (h t) q y<
      Real.exp (-σ*(2*n : ℕ)*K*τ)*(derivativeRadius r k-derivativeRadius r (k+1))/4 := by
    rw [derivativeCutoffRadius_eq_buffer]
    exact hshort
  obtain ⟨E,hE,hval,hupper,hgrad,hlap,htime⟩ := hBuild
    (derivativeRadius r (k+1)) (derivativeRadius r k) (derivativeRadius_pos hr (k+1))
      (derivativeRadius_succ_lt hr k) (derivativeRadius_le_two_mul hr k) q hq y t htI hshort'
  exact exists_timeDistanceCutoff_lowerSupport_of_upperSupport h q y
    (derivativeCutoffRadius n K r τ σ (k+1)) K σ t hR hK.le hσ.le hh E
      hE hval hupper hgrad hlap htime hshort

end Yau.LeafProofs.L23Aux
