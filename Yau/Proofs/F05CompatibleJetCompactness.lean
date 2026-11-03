import Yau.Proofs.F05CompatibleJetLimit
import Yau.Proofs.F05FiniteJetSubsequence
import Yau.Proofs.F05BootstrapSchauderLimit

/-! Finite Arzelà–Ascoli and the genuine closed FTC/overlap graphs produce
one compatible limiting jet. All four limits are constructed internally. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

abbrev F05CompleteJet (n : ℕ) := (ℝ × F05Dual n) × (F05Hessian n × ℝ)

def F05JetComponentTuple {α : ℝ} {Q : Set (Point n)} (u : F05JetComponent α Q) :
    Point n → F05CompleteJet n := fun p =>
  ((F05BCFFun u.1 p,F05BCFFun u.2.1 p),
    (vectorHolderFun u.2.2.1 p,holderGraphFun u.2.2.2 p))

theorem F05_compatible_jet_compact_subsequence (A : AtlasData M) {α C T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (u : ℕ → F05CompatibleJetGraph A (α/2) hT)
    (hTuple : ∀ k i, HolderBound α (F05Q A i T) (F05JetComponentTuple ((u k).val i).val) C) :
    ∃ (φ : ℕ → ℕ) (uLim : F05CompatibleJetGraph A (α/2) hT), StrictMono φ ∧
      Tendsto (fun k => u (φ k)) atTop (𝓝 uLim) := by
  obtain ⟨φ,g,hφ,hg⟩ := F05_finite_holder_compact_subsequence hα
    (fun i => F05Q A i T)
    (fun i => (F05_region_isCompact (A.normal i) 2).prod isCompact_Icc)
    (fun k i => F05JetComponentTuple ((u k).val i).val) hTuple
  have hV (i : Fin A.count) : UniformCauchySeqOn
      (fun k => F05BCFFun ((u (φ k)).val i).val.1) atTop (F05Q A i T) :=
    (uniformContinuous_fst.comp_tendstoUniformlyOn
      (uniformContinuous_fst.comp_tendstoUniformlyOn (hg i))).uniformCauchySeqOn
  have hG (i : Fin A.count) : UniformCauchySeqOn
      (fun k => F05BCFFun ((u (φ k)).val i).val.2.1) atTop (F05Q A i T) :=
    (uniformContinuous_snd.comp_tendstoUniformlyOn
      (uniformContinuous_fst.comp_tendstoUniformlyOn (hg i))).uniformCauchySeqOn
  have hH (i : Fin A.count) : UniformCauchySeqOn
      (fun k => vectorHolderFun ((u (φ k)).val i).val.2.2.1) atTop (F05Q A i T) :=
    (uniformContinuous_fst.comp_tendstoUniformlyOn
      (uniformContinuous_snd.comp_tendstoUniformlyOn (hg i))).uniformCauchySeqOn
  have hJ (i : Fin A.count) : UniformCauchySeqOn
      (fun k => holderGraphFun ((u (φ k)).val i).val.2.2.2) atTop (F05Q A i T) :=
    (uniformContinuous_snd.comp_tendstoUniformlyOn
      (uniformContinuous_snd.comp_tendstoUniformlyOn (hg i))).uniformCauchySeqOn
  obtain ⟨uLim,hLim⟩ := F05_compatible_jet_half_limit A hT (fun k => u (φ k))
    (fun i k => holderBound_fst (holderBound_snd (hTuple (φ k) i)))
    (fun i k => holderBound_snd (holderBound_snd (hTuple (φ k) i))) hV hG hH hJ
  exact ⟨φ,uLim,hφ,hLim⟩

end Yau.Proofs.F05Aux
