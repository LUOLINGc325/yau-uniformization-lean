import Yau.LeafProofs.L12IndexAnalysis

/-! Analytic contradiction for a broken-energy first-derivative field. -/

open Filter
open scoped Topology

namespace Yau.LeafProofs.L12Aux

/-- Differentiate the actual first-derivative field when both momenta vanish at the
base point. Continuity of the coefficients suffices for this derivative. -/
theorem hasFDerivAt_broken_energy_field
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {L0 : E × G → F →L[ℝ] (E × G →L[ℝ] ℝ)}
    {L1 : E × G → G →L[ℝ] (E × G →L[ℝ] ℝ)}
    {m0 : E × G → F} {m1 : E × G → G} {z : E × G}
    {m0' : E × G →L[ℝ] F} {m1' : E × G →L[ℝ] G}
    (hL0 : ContinuousAt L0 z) (hL1 : ContinuousAt L1 z)
    (hm0 : HasFDerivAt m0 m0' z) (hm1 : HasFDerivAt m1 m1' z)
    (hm00 : m0 z = 0) (hm10 : m1 z = 0) :
    HasFDerivAt (fun q => L0 q (m0 q) + L1 q (m1 q))
      ((L0 z).comp m0' + (L1 z).comp m1') z := by
  exact (hasFDerivAt_clm_apply_of_zero hL0 hm0 hm00).add
    (hasFDerivAt_clm_apply_of_zero hL1 hm1 hm10)

/-- A broken-energy derivative field with a positive endpoint mixed term cannot
occur at a local minimum. The Hessian here is derived from the actual derivative
field near the base point. -/
theorem not_localMin_of_broken_energy_mixed_positive
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × G → ℝ}
    {L0 : E × G → F →L[ℝ] (E × G →L[ℝ] ℝ)}
    {L1 : E × G → G →L[ℝ] (E × G →L[ℝ] ℝ)}
    {m0 : E × G → F} {m1 : E × G → G} {z : E × G}
    {m0' : E × G →L[ℝ] F} {m1' : E × G →L[ℝ] G}
    (hL0 : ContinuousAt L0 z) (hL1 : ContinuousAt L1 z)
    (hm0 : HasFDerivAt m0 m0' z) (hm1 : HasFDerivAt m1 m1' z)
    (hm00 : m0 z = 0) (hm10 : m1 z = 0)
    (hfirst : ∀ᶠ q in 𝓝 z,
      HasFDerivAt f (L0 q (m0 q) + L1 q (m1 q)) q)
    (v : E × G) (K : G)
    (hv0 : m0' v = 0) (hv1 : m1' v = K) (hv2 : v.2 = 0)
    (B : G →L[ℝ] G →L[ℝ] ℝ)
    (hL1endpoint : ∀ a h, L1 z a h = B a h.2)
    (hKpos : 0 < B K K) :
    ¬ IsLocalMin f z := by
  intro hmin
  let f' : E × G → E × G →L[ℝ] ℝ :=
    fun q => L0 q (m0 q) + L1 q (m1 q)
  let H : E × G →L[ℝ] E × G →L[ℝ] ℝ :=
    (L0 z).comp m0' + (L1 z).comp m1'
  have hfirst' : ∀ᶠ q in 𝓝 z, HasFDerivAt f (f' q) q := hfirst
  have hsecond : HasFDerivAt f' H z :=
    hasFDerivAt_broken_energy_field hL0 hL1 hm0 hm1 hm00 hm10
  have hnull : H v v = 0 := by
    simp [H, hv0, hv1, hL1endpoint, hv2]
  have hmixed : H v (0, K) = B K K := by
    simp [H, hv0, hv1, hL1endpoint]
  have hvanish : H v (0, K) = 0 :=
    localMin_hessian_null hmin hfirst' hsecond hnull (0, K)
  exact (ne_of_gt hKpos) (hmixed.symm.trans hvanish)

end Yau.LeafProofs.L12Aux
