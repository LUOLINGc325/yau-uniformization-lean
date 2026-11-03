import Yau.Proofs.F05BootstrapCompactHolder
import Yau.Proofs.F05BootstrapUniformJetLimit

/-! A common relative Schauder bound is closed under uniform convergence of
the values. An actual compact subsequence of the four-jet tuple is constructed
inside the proof, then the derivative-limit calculus identifies every jet. -/

open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux

theorem F05_holderBound_prod_same {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W] {Q : Set (Point n)} {α C : ℝ}
    {f : Point n → V} {g : Point n → W}
    (hf : HolderBound α Q f C) (hg : HolderBound α Q g C) :
    HolderBound α Q (fun z => (f z,g z)) C := by
  refine ⟨hf.1,?_,?_⟩
  · intro z hz
    exact max_le (hf.2.1 z hz) (hg.2.1 z hz)
  · intro z hz w hw
    exact max_le (hf.2.2 z hz w hw) (hg.2.2 z hz w hw)

theorem F05_relSchauder_limit {n : ℕ} (ν : Option (RIdx n)) {r s T α C : ℝ}
    (hr : 0 < r) (hsT : s < T) (hα : 0 < α)
    {v : ℕ → Point n → ℝ} {vLim : Point n → ℝ}
    (hv : ∀ k, F05RelSchauder α (region ν r) (Icc s T) (v k) C)
    (hLim : TendstoUniformlyOn v vLim atTop (region ν r ×ˢ Icc s T)) :
    F05RelSchauder α (region ν r) (Icc s T) vLim C := by
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
  apply F05_relative_schauder_uniform_jets ν hr hsT (fun k => hv (φ k)) hLimSub
  · exact uniformContinuous_snd.comp_tendstoUniformlyOn
      (uniformContinuous_fst.comp_tendstoUniformlyOn hg)
  · exact uniformContinuous_fst.comp_tendstoUniformlyOn
      (uniformContinuous_snd.comp_tendstoUniformlyOn hg)
  · exact uniformContinuous_snd.comp_tendstoUniformlyOn
      (uniformContinuous_snd.comp_tendstoUniformlyOn hg)

end Yau.Proofs.F05Aux
