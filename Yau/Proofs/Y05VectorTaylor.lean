import Yau.Proofs.Y05FiniteJets

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment
open scoped ContDiff

variable {n : ℕ}

/-- The coordinate Taylor polynomials represent every actual mixed Fréchet
derivative of a holomorphic vector germ. -/
theorem exists_vector_taylor {f : ComplexVector n → ComplexVector n}
    (hf : AnalyticAt ℂ f 0) (d : ℕ) :
    ∃ P : PolyMap n, P.degree ≤ d ∧ GermJetEq P.eval f d ∧
      (f 0 = 0 → P.FixesZero) := by
  have hfa (i : Fin n) : AnalyticAt ℂ (fun z => f z i) 0 :=
    ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).analyticAt (f 0)).comp hf
  choose P hPdeg hPjet using (fun i : Fin n => exists_scalar_taylor (hfa i) d)
  have hP : PolyMap.degree P ≤ d := by
    unfold PolyMap.degree
    exact Finset.sup_le fun i hi => hPdeg i
  refine ⟨P, hP, ?_, ?_⟩
  · intro m hm
    ext v i
    let L : ComplexVector n →L[ℂ] ℂ := EuclideanSpace.proj i
    have hPsmooth : ContDiffAt ℂ m (PolyMap.eval P) 0 :=
      ((Yau.Proofs.Y01Aux.polyMap_eval_contDiff P).of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have hFsmooth : ContDiffAt ℂ m f 0 := hf.contDiffAt
    have hPd := L.iteratedFDeriv_comp_left (x := 0) hPsmooth (le_refl (m : ℕ∞ω))
    have hFd := L.iteratedFDeriv_comp_left (x := 0) hFsmooth (le_refl (m : ℕ∞ω))
    have hPv := congrArg (fun D => D v) hPd
    have hFv := congrArg (fun D => D v) hFd
    have hJv := congrArg (fun D => D v) (hPjet i m hm)
    change iteratedFDeriv ℂ m (scalarEval (P i)) 0 v =
      (iteratedFDeriv ℂ m (PolyMap.eval P) 0 v) i at hPv
    change iteratedFDeriv ℂ m (fun z => f z i) 0 v =
      (iteratedFDeriv ℂ m f 0 v) i at hFv
    exact hPv.symm.trans (hJv.trans hFv)
  · intro hf0 i
    rw [coefficient_zero_of_scalarJetEq (hPjet i), hf0]
    rfl

end Yau.Proofs.Y05Aux
