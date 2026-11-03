import Yau.Proofs.P06HodgeRegularityLeibnizWords
import Yau.Proofs.P06HodgeRegularityWeakSums

/-! Compact localization of finite actual weak jets by the ordered Leibniz
rule. Every resulting jet is genuinely whole-space L² and compactly supported. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsLocallyFiniteMeasure ν]

theorem regularityWeakJet_compact_cutoff
    {O : Set E} (hO : IsOpen O) (v : ι → E) (s : ℕ)
    (U : E → α → ℝ) (J : List ι → E → α → ℝ)
    (hJ : regularityWeakJet ν O v s U J)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχO : tsupport χ ⊆ O) :
    regularityWeakJet ν Set.univ v s (fun z c => χ z * U z c) (regularityLeibnizJet v χ J) ∧
      ∀ w c, tsupport (fun z => regularityLeibnizJet v χ J w z c) ⊆ tsupport χ := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · funext z c
    rw [regularityLeibnizJet_nil, hJ.1]
  · intro w hw c
    simp only [Measure.restrict_univ]
    change MemLp (fun z => ((regularityWordSplits w).map
      (fun st => regularityCoefficientWord v st.1 χ z * J st.2 z c)).sum) 2 ν
    apply regularityMemLp_list_sum ν (regularityWordSplits w)
      (fun st z => regularityCoefficientWord v st.1 χ z * J st.2 z c)
    intro st hst
    have hlen := regularityWordSplits_lengths w st hst
    have hr := regularityCoefficientWord_regular v hχ hcχ st.1
    exact regularityCompact_mul_memLp ν hO hr.1 hr.2.1 (hr.2.2.trans hχO)
      (hJ.2.1 st.2 (by omega) c)
  · intro w hw i c
    let F := fun (st : List ι × List ι) (z : E) => regularityCoefficientWord v st.1 χ z * J st.2 z c
    let D := fun (st : List ι × List ι) (z : E) => regularityCoefficientWord v (i::st.1) χ z * J st.2 z c +
      regularityCoefficientWord v st.1 χ z * J (i::st.2) z c
    have hDfun (st : List ι × List ι) : D st = fun z =>
        regularityCoefficientWord v st.1 χ z * J (i::st.2) z c +
          fderiv ℝ (regularityCoefficientWord v st.1 χ) z (v i) * J st.2 z c := by
      funext z
      change fderiv ℝ (regularityCoefficientWord v st.1 χ) z (v i) * J st.2 z c +
          regularityCoefficientWord v st.1 χ z * J (i::st.2) z c = _
      exact add_comm _ _
    have hEach (st : List ι × List ι) (hst : st ∈ regularityWordSplits w) :
        MemLp (F st) 2 ν ∧ MemLp (D st) 2 ν ∧
          regularityWeakDeriv ν Set.univ (v i) (F st) (D st) := by
      have hlen := regularityWordSplits_lengths w st hst
      have hr := regularityCoefficientWord_regular v hχ hcχ st.1
      have hl := regularityWeakDeriv_localize ν hO
        (hJ.2.1 st.2 (by omega) c)
        (hJ.2.1 (i::st.2) (by simp only [List.length_cons]; omega) c)
        (hJ.2.2 st.2 (by omega) i c) hr.1 hr.2.1 (hr.2.2.trans hχO)
      refine ⟨hl.1, ?_, ?_⟩
      · rw [hDfun]
        exact hl.2.1
      · rw [hDfun]
        exact hl.2.2
    have hs := regularityWeakDeriv_list_sum ν (O := Set.univ) (v i) (regularityWordSplits w) F D
      (fun st hst => by simpa only [Measure.restrict_univ] using (hEach st hst).1)
      (fun st hst => by simpa only [Measure.restrict_univ] using (hEach st hst).2.1)
      (fun st hst => (hEach st hst).2.2)
    have hEq : (fun z => ((regularityWordSplits w).map (fun st => D st z)).sum) =
        fun z => regularityLeibnizJet v χ J (i::w) z c := by
      funext z
      exact (regularityLeibnizJet_cons v χ J w i z c).symm
    rw [hEq] at hs
    exact hs
  · intro w c
    apply closure_minimal ?_ (isClosed_tsupport χ)
    intro z hz
    by_contra hzχ
    apply hz
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨st, _hst, rfl⟩ := List.mem_map.mp ha
    have hr := regularityCoefficientWord_regular v hχ hcχ st.1
    rw [image_eq_zero_of_notMem_tsupport (fun h => hzχ (hr.2.2 h)), zero_mul]

end Yau.NodeProofs.P06Aux
