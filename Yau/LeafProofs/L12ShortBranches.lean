import Yau.LeafProofs.L12EndpointEnergy
import Yau.LeafProofs.L12PhaseVariation
import Yau.LeafProofs.L12BrokenEnergy

/-! Genuine short endpoint branches, including a branch obtained by reversing
the actual complete geodesic. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- Reversing a genuine endpoint branch preserves its actual local inverse
property. This lets the short segment be chosen at a fixed terminal phase. -/
theorem exists_realGeodesic_endpointBranch_reversed (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (d : ℝ)
    (hdet : (realGeodesicJacobiMatrix g (realSegmentReverse g d q) d).det ≠ 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ U : Set (M.Carrier × M.Carrier), IsOpen U ∧ realGeodesicEndpointMap g d q ∈ U ∧
      ∃ P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
        ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U ∧
        P (realGeodesicEndpointMap g d q) = q ∧
        (∀ z ∈ U, (P z).proj = z.1 ∧ (realGeodesicFlow g (P z) d).proj = z.2) ∧
        (∀ᶠ q' in 𝓝 q, P (realGeodesicEndpointMap g d q') = q') := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let qR := realSegmentReverse g d q
  obtain ⟨U, hU, hqU, P, hP, hPq, hends, hleft⟩ :=
    exists_realGeodesic_endpointBranch g qR d hdet
  have hswap (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
      realGeodesicEndpointMap g d (realSegmentReverse g d p) =
        (realGeodesicEndpointMap g d p).swap := realSegmentReverse_endpointMap g d p
  have hsc : ContMDiff (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1
      (Prod.swap : M.Carrier × M.Carrier → M.Carrier × M.Carrier) :=
    contMDiff_snd.prodMk contMDiff_fst
  let V := Prod.swap ⁻¹' U
  let Q := fun z : M.Carrier × M.Carrier => realSegmentReverse g d (P z.swap)
  have hV : IsOpen V := hU.preimage continuous_swap
  have hqV : realGeodesicEndpointMap g d q ∈ V := by
    change (realGeodesicEndpointMap g d q).swap ∈ U
    rw [← hswap]
    exact hqU
  refine ⟨V, hV, hqV, Q, ?_, ?_, ?_, ?_⟩
  · exact (realSegmentReverse_contMDiff g d).comp_contMDiffOn
      (hP.comp hsc.contMDiffOn (fun _ hz => hz))
  · dsimp only [Q]
    rw [← hswap q, hPq]
    exact realSegmentReverse_involutive g d q
  · intro z hz
    have he := hends z.swap hz
    have hr := realSegmentReverse_endpointMap g d (P z.swap)
    have hi := congrArg Prod.fst hr
    have ht := congrArg Prod.snd hr
    exact ⟨hi.trans he.2, ht.trans he.1⟩
  · have hcont : ContinuousAt (realSegmentReverse g d) q :=
      (realSegmentReverse_contMDiff g d).continuous.continuousAt
    have hevent : ∀ᶠ p in 𝓝 q,
        P (realGeodesicEndpointMap g d (realSegmentReverse g d p)) =
          realSegmentReverse g d p := hcont.tendsto.eventually hleft
    filter_upwards [hevent] with p hp
    dsimp only [Q]
    rw [← hswap, hp, realSegmentReverse_involutive]

/-- Two nonsingular short pieces can be selected about any interior time.
The backwards piece is chosen at the fixed middle phase, so no uniform
injectivity radius is used. -/
theorem exists_realGeodesic_short_nonsingular_segments (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {τ T : ℝ}
    (hτ : 0 < τ) (hτT : τ < T) :
    ∃ s e d : ℝ, 0 < s ∧ 0 < e ∧ 0 < d ∧ s + e = τ ∧ s + e + d < T ∧
      (realGeodesicJacobiMatrix g
        (realSegmentReverse g e (realGeodesicFlow g p s)) e).det ≠ 0 ∧
      (realGeodesicJacobiMatrix g (realGeodesicFlow g p τ) d).det ≠ 0 := by
  let q := realGeodesicFlow g p τ
  let qR := realPhaseScale (-1) q
  have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < τ :=
    (eventually_lt_nhds hτ).filter_mono nhdsWithin_le_nhds
  have hep : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
  obtain ⟨e, hepos, helt, hedet⟩ :=
    (hep.and (hsmall.and (realGeodesicJacobiMatrix_det_pos_near_zero g qR))).exists
  have hes : 0 < e := hepos
  have hdsmall : ∀ᶠ d in 𝓝[>] (0 : ℝ), d < T - τ :=
    (eventually_lt_nhds (sub_pos.mpr hτT)).filter_mono nhdsWithin_le_nhds
  obtain ⟨d, hdpos, hdlt, hddet⟩ :=
    (hep.and (hdsmall.and (realGeodesicJacobiMatrix_det_pos_near_zero g q))).exists
  have hds : 0 < d := hdpos
  refine ⟨τ - e, e, d, sub_pos.mpr helt, hes, hds, by ring, by linarith, ?_, ne_of_gt hddet⟩
  have hrev : realSegmentReverse g e (realGeodesicFlow g p (τ - e)) = qR := by
    dsimp only [realSegmentReverse, qR, q]
    rw [← realGeodesicFlow_add]
    congr 1
    ring
  rw [hrev]
  exact ne_of_gt hedet

end Yau.LeafProofs.L12Aux
