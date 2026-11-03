import Yau.Proofs.P06HodgeRegularityFormalLocalH1
import Yau.Proofs.P06HodgeRegularityBuffers

/-! A genuine local H¹ gain with all cutoffs and energy buffers chosen
internally. Its ellipticity constant precedes the input fields. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α] [DecidableEq α]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]

theorem regularityForwardWeak_local_h1
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {O V : Set E} (hO : IsOpen O) (hV : IsOpen V)
    (hcV : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (ell : ℝ) (hell : 0 < ell)
    (hcoercive : ∀ z ∈ O, ∀ ξ : ι → ℝ,
      ell * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, q i j z * ξ j * ξ i)
    (U W : E → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hW : ∀ c, MemLp (fun z => W z c) 2 (ν.restrict O))
    (hweak : regularityForwardWeak ν O v q e1 e0 U W) :
    ∃ G : E → ι → α → ℝ,
      (∀ i c, MemLp (fun z => G z i c) 2 (ν.restrict V)) ∧
      ∀ i c, regularityWeakDeriv ν V (v i) (fun z => U z c) (fun z => G z i c) := by
  obtain ⟨B, hB, hVB, hBO, hcB⟩ := exists_open_between_and_isCompact_closure hcV hO hVO
  obtain ⟨χ,hχ,hcχ,hχB,_,hχone⟩ := regularity_exists_compact_cutoff hB hcV hVB
  have hχO : tsupport χ ⊆ O := hχB.trans (subset_closure.trans hBO)
  obtain ⟨G,hG,hd⟩ := regularityForwardWeak_cutoff_h1 ν v q e1 e0 hq hcq he1 hce1 he0 hce0
    hO ⟨hχ,hcχ,hχO⟩ U W hU hW hweak B hB hcB hχB ell hell
    (fun z hz ξ => regularityScalarSystemA_coercive q z ell (hcoercive z (hBO hz)) ξ)
  refine ⟨G,fun i c => (hG i c).restrict V,?_⟩
  intro i c
  have hh := regularityWeakDeriv_mono ν (hd i c) (Set.subset_univ V)
  exact regularityWeakDeriv_congr_on ν hV hh
    (fun z hz => by rw [hχone z (subset_closure hz),one_mul]) (fun _ _ => rfl)

end Yau.NodeProofs.P06Aux
