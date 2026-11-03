import Yau.Proofs.P03DeterminantTransitions

open scoped Manifold Topology ContDiff
open Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem determinantTransition_eq_coordChange (a b x : M.Carrier)
    (ha : x ∈ (extChartAt (ComplexModel n) a).source)
    (hb : x ∈ (extChartAt (ComplexModel n) b).source) :
    determinantTransition a b x =
      ((trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a).coordChangeL ℂ
        (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) b) x :
          ComplexVector n →L[ℂ] ComplexVector n) := by
  have ha' : x ∈ (chartAt (ComplexVector n) a).source := by simpa using ha
  have hb' : x ∈ (chartAt (ComplexVector n) b).source := by simpa using hb
  have hta : x ∈ (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a).baseSet :=
    by simpa only [TangentBundle.trivializationAt_baseSet] using ha'
  have htb : x ∈ (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) b).baseSet :=
    by simpa only [TangentBundle.trivializationAt_baseSet] using hb'
  apply ContinuousLinearMap.ext
  intro v
  change determinantTransition a b x v =
    (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a).coordChangeL ℂ
      (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) b) x v
  rw [Trivialization.coordChangeL_apply _ _ ⟨hta, htb⟩]
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ htb]
  rw [← Trivialization.symmL_apply (R := ℂ) _ hta]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hb',
    TangentBundle.symmL_trivializationAt ha', ModelWithCorners.range_eq_univ,
    mfderivWithin_univ]
  rfl

theorem determinantTransition_contMDiffOn (a b : M.Carrier) :
    ContMDiffOn (ComplexModel n) 𝓘(ℂ, ComplexVector n →L[ℂ] ComplexVector n) ⊤
      (determinantTransition a b)
      ((extChartAt (ComplexModel n) a).source ∩ (extChartAt (ComplexModel n) b).source) := by
  have h := contMDiffOn_coordChangeL (IB := ComplexModel n) (n := (⊤ : ℕ∞ω))
    (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) a)
    (trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) b)
  simp only [TangentBundle.trivializationAt_baseSet] at h
  simp only [extChartAt_source]
  apply h.congr
  intro x hx
  exact determinantTransition_eq_coordChange a b x
    (by simpa only [extChartAt_source] using hx.1)
    (by simpa only [extChartAt_source] using hx.2)

end Yau.NodeProofs.P03Aux
