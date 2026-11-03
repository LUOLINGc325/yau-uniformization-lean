import Yau.Proofs.F05BootstrapSchauderEquationLimit
import Yau.Proofs.F05EventualNonlinearJetEquation

/-! The genuine nonlinear equation is closed under a common relative
Schauder bound and uniform value convergence. The proof constructs its
own finite tuple subsequence and identifies all actual limiting jets. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_nonlinear_relative_schauder_limit (ν : Option (RIdx n)) {r s T α C : ℝ}
    (hr : 0 < r) (hsT : s < T) (hα : 0 < α)
    {v : ℕ → Point n → ℝ} {vLim : Point n → ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (R : Point n → ℝ)
    (hv : ∀ k, F05RelSchauder α (region ν r) (Icc s T) (v k) C)
    (hLim : TendstoUniformlyOn v vLim atTop (region ν r ×ˢ Icc s T))
    (hEq : ∀ k z, z ∈ region ν r ×ˢ Icc s T →
      F05RelT (Icc s T) (v k) z = Real.exp (-v k z)*
        ((∑ i,∑ j,a z i j*F05RelDD (region ν r) (v k) z (realVec i) (realVec j))+
          ∑ i,b z i*F05RelD (region ν r) (v k) z (realVec i))+(1-Real.exp (-v k z))*R z) :
    F05RelSchauder α (region ν r) (Icc s T) vLim C ∧
      ∀ z ∈ region ν r ×ˢ Icc s T,
        F05RelT (Icc s T) vLim z = Real.exp (-vLim z)*
          ((∑ i,∑ j,a z i j*F05RelDD (region ν r) vLim z (realVec i) (realVec j))+
            ∑ i,b z i*F05RelD (region ν r) vLim z (realVec i))+(1-Real.exp (-vLim z))*R z := by
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
  have hVLim := uniformContinuous_fst.comp_tendstoUniformlyOn
    (uniformContinuous_fst.comp_tendstoUniformlyOn hg)
  have hGLim := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_fst.comp_tendstoUniformlyOn hg)
  have hHLim := uniformContinuous_fst.comp_tendstoUniformlyOn
    (uniformContinuous_snd.comp_tendstoUniformlyOn hg)
  have hJLim := uniformContinuous_snd.comp_tendstoUniformlyOn
    (uniformContinuous_snd.comp_tendstoUniformlyOn hg)
  have hIdent := F05_relative_uniform_jets_identified ν hr hsT (fun k => hv (φ k))
    hLimSub hGLim hHLim hJLim
  refine ⟨F05_relative_schauder_uniform_jets ν hr hsT (fun k => hv (φ k))
    hLimSub hGLim hHLim hJLim,?_⟩
  intro z hz
  have hActual := F05_eventual_nonlinear_jet_equation (a z) (b z) (R z)
    (fun k => v (φ k) z)
    (fun k => F05RelD (region ν r) (v (φ k)) z)
    (fun k => F05RelDD (region ν r) (v (φ k)) z)
    (fun k => F05RelT (Icc s T) (v (φ k)) z)
    (hLimSub.tendsto_at hz) (hGLim.tendsto_at hz) (hHLim.tendsto_at hz) (hJLim.tendsto_at hz)
    (Eventually.of_forall (fun k => hEq (φ k) z hz))
  rw [(hIdent z hz).1,(hIdent z hz).2.1,(hIdent z hz).2.2]
  exact hActual

end Yau.Proofs.F05Aux
