import Yau.Proofs.F05BootstrapSchauderLimit
import Yau.Proofs.F05BootstrapEquationLimit

/-! Common Schauder bounds and uniform value convergence preserve the
actual PDE. All limiting jets and their subsequence are constructed inside
the proof; no limiting-jet or regularity premise is supplied. -/

open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relSchauder_equation_limit (ν : Option (RIdx n)) {r s T α C : ℝ}
    (hr : 0 < r) (hsT : s < T) (hα : 0 < α)
    {v : ℕ → Point n → ℝ} {vLim : Point n → ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    {f : ℕ → Point n → ℝ} {fLim : Point n → ℝ}
    (hv : ∀ k, F05RelSchauder α (region ν r) (Icc s T) (v k) C)
    (hLim : TendstoUniformlyOn v vLim atTop (region ν r ×ˢ Icc s T))
    (hfLim : ∀ z ∈ region ν r ×ˢ Icc s T, Tendsto (fun k => f k z) atTop (𝓝 (fLim z)))
    (hEq : ∀ k z, z ∈ region ν r ×ˢ Icc s T →
      F05RelOp (region ν r) (Icc s T) a b (v k) z = f k z) :
    F05RelSchauder α (region ν r) (Icc s T) vLim C ∧
      ∀ z ∈ region ν r ×ˢ Icc s T, F05RelOp (region ν r) (Icc s T) a b vLim z = fLim z := by
  let Jets : ℕ → Point n →
      (ℝ × (Space n →L[ℝ] ℝ)) × ((Space n →L[ℝ] Space n →L[ℝ] ℝ) × ℝ) :=
    fun k z => ((v k z,F05RelD (region ν r) (v k) z),
      (F05RelDD (region ν r) (v k) z,F05RelT (Icc s T) (v k) z))
  have hJets : ∀ k, HolderBound α (region ν r ×ˢ Icc s T) (Jets k) C :=
    fun k => F05_holderBound_prod_same (hv k).2.1
      (F05_holderBound_prod_same (hv k).2.2.1 (hv k).2.2.2)
  obtain ⟨φ,g,hφ,hg⟩ := F05_holder_compact_subsequence hα
    ((F05_region_isCompact ν r).prod isCompact_Icc) hJets
  have hLimSub : TendstoUniformlyOn (fun k => v (φ k)) vLim atTop
      (region ν r ×ˢ Icc s T) :=
    fun U hU => hφ.tendsto_atTop.eventually (hLim U hU)
  have hGLim := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_fst.comp_tendstoUniformlyOn hg)
  have hHLim := uniformContinuous_fst.comp_tendstoUniformlyOn
    (uniformContinuous_snd.comp_tendstoUniformlyOn hg)
  have hJLim := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_snd.comp_tendstoUniformlyOn hg)
  refine ⟨F05_relative_schauder_uniform_jets ν hr hsT (fun k => hv (φ k))
    hLimSub hGLim hHLim hJLim,?_⟩
  apply F05_relative_equation_uniform_jets_limit ν hr hsT a b (fun k => hv (φ k))
    hLimSub hGLim hHLim hJLim
  · intro z hz
    exact (hfLim z hz).comp hφ.tendsto_atTop
  · intro k z hz
    exact hEq (φ k) z hz

end Yau.Proofs.F05Aux
