import Yau.Proofs.V02AreaTaylorJet
import Mathlib.Analysis.Normed.Module.Normalize

/-! A smooth quadratic density has uniformly bounded parameter jets on
compact position ranges, with exactly quadratic growth in the disc velocity. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem compact_quadratic_parameter_jet_bound
    {O : Set (ℂ × D)} (hO : IsOpen O) {q : ℂ × (D × V) → ℝ}
    (hq : ContDiffOn ℝ ∞ q {p | (p.1, p.2.1) ∈ O})
    (hscale : ∀ p ∈ O, ∀ v : V, ∀ t : ℝ, q (p.1, (p.2, t • v)) =
      t ^ 2 * q (p.1, (p.2, v)))
    {K : Set (ℂ × D)} (hK : IsCompact K) (hKO : K ⊆ O) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ v : V,
      ‖iteratedFDeriv ℝ k (fun z => q (z, (p.2, v))) p.1‖ ≤ C * ‖v‖ ^ 2 := by
  let T : (ℂ × D) × V → ℂ × (D × V) := fun p => (p.1.1, (p.1.2, p.2))
  have hT : Continuous T := continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  let Kfull := T '' (K ×ˢ Metric.closedBall (0 : V) 1)
  have hKfull : IsCompact Kfull := (hK.prod (isCompact_closedBall _ _)).image hT
  have hopen : IsOpen {p : ℂ × (D × V) | (p.1, p.2.1) ∈ O} :=
    hO.preimage (continuous_fst.prodMk continuous_snd.fst)
  have hsub : Kfull ⊆ {p : ℂ × (D × V) | (p.1, p.2.1) ∈ O} := by
    rintro p ⟨a, ha, rfl⟩
    exact hKO ha.1
  obtain ⟨C, hC, hbound⟩ := compact_slice_jet_bound hopen hq hKfull hsub k
  refine ⟨C, hC, fun p hp v => ?_⟩
  let vn := NormedSpace.normalize v
  have hvn : vn ∈ Metric.closedBall (0 : V) 1 := inv_norm_smul_mem_unitClosedBall v
  have hpvn : (p.1, (p.2, vn)) ∈ Kfull := ⟨(p, vn), ⟨hp, hvn⟩, rfl⟩
  have hunit := hbound _ hpvn
  have hcont : ContDiffAt ℝ k (fun z => q (z, (p.2, vn))) p.1 :=
    (((hq.contDiffAt (hopen.mem_nhds (hKO hp))).comp p.1
      (contDiffAt_id.prodMk contDiffAt_const))).of_le (by simp)
  have heq : (fun z => q (z, (p.2, v))) =ᶠ[𝓝 p.1]
      (fun z => (‖v‖ ^ 2 : ℝ) • q (z, (p.2, vn))) := by
    have hn := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hO.mem_nhds (hKO hp))
    filter_upwards [hn] with z hz
    simpa only [vn, NormedSpace.norm_smul_normalize, smul_eq_mul] using
      hscale (z, p.2) hz vn ‖v‖
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' hcont, norm_smul,
    Real.norm_of_nonneg (sq_nonneg ‖v‖)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖v‖)

end Yau.Blueprint.V02AreaTaylorProof
