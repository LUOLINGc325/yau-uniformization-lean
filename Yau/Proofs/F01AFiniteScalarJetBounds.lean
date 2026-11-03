import Yau.Proofs.F01APositiveJetCompactRange
import Yau.Proofs.F01FiniteLogDetSpatialJet
import Yau.Proofs.F01RealHessianContractionCLM
import Yau.Proofs.F01SecondSpatialJetCurrying

/-! The negative scalar curvature is a continuous expression of the
actual finite spatial matrix jet. A uniform positive zeroth-order lower
bound and bounds through order two therefore give a finite scalar bound. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

def finiteNegativeScalarJet
    (p : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) 2) : ℝ :=
  realHessianContractionCLM (scalarSymbol (matrixFiniteJetValue 2 p))
    (secondSpatialJetCurryingCLM (finiteLogDetSpatialJet 2 p))

theorem finiteNegativeScalarJet_contDiffOn :
    ContDiffOn ℝ ∞ (finiteNegativeScalarJet (n := n))
      {p | 0 < (matrixFiniteJetValue 2 p).det.re} := by
  have hsymbol := scalarSymbol_contDiffOn_nonsingular.comp
    (matrixFiniteJetValue_contDiff (n := n) 2).contDiffOn
    (show ∀ p : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) 2,
      p ∈ {p | 0 < (matrixFiniteJetValue 2 p).det.re} →
      matrixFiniteJetValue 2 p ∈ {H | H.det ≠ 0} from by
        intro p hp hzero
        change 0 < (matrixFiniteJetValue 2 p).det.re at hp
        simp only [hzero, Complex.zero_re, lt_self_iff_false] at hp)
  have hsecond := secondSpatialJetCurryingCLM.contDiff.comp_contDiffOn
    (finiteLogDetSpatialJet_contDiffOn (n := n) 2)
  exact (realHessianContractionCLM.contDiff.comp_contDiffOn hsymbol).clm_apply hsecond

theorem finiteNegativeScalarJet_native
    {H : Space n → Matrix (Fin n) (Fin n) ℂ} {x : Space n}
    (hH : ContDiffAt ℝ ∞ H x) (hPos : 0 < (H x).det.re) :
    finiteNegativeScalarJet (fun j => iteratedFDeriv ℝ j.val H x) =
      -traceWith (H x) (backgroundRicci H x) := by
  have hLog : ContDiffAt ℝ ∞ (fun z => Real.log (H z).det.re) x :=
    (complexMatrixLogDet_contDiffOn.contDiffAt
      (positive_real_determinant_domain_isOpen.mem_nhds hPos)).comp x hH
  unfold finiteNegativeScalarJet
  rw [finiteLogDetSpatialJet_native hH hPos 2, secondSpatialJetCurryingCLM_native]
  change realHessianContractionCLM (scalarSymbol (H x))
    (fderiv ℝ (fderiv ℝ (fun z => Real.log (H z).det.re)) x) = _
  exact (native_background_source_contraction (H x) H (hLog.of_le (by simp))).symm

theorem finite_negative_scalar_uniform_bound {ell R : ℝ}
    (hell : 0 < ell) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ (H : Space n → Matrix (Fin n) (Fin n) ℂ) (x : Space n),
      ContDiffAt ℝ ∞ H x →
      (H x - (ell : ℂ) • 1).PosSemidef →
      (∀ k : Fin 3, ‖iteratedFDeriv ℝ k.val H x‖ ≤ R) →
      |traceWith (H x) (backgroundRicci H x)| ≤ B := by
  obtain ⟨B, hB, hb⟩ := positive_matrix_finite_jet_expression_budget 2 hell hR
    (finiteNegativeScalarJet (n := n)) finiteNegativeScalarJet_contDiffOn.continuousOn
  refine ⟨B, hB, ?_⟩
  intro H x hH hlo hjet
  have hpos : (H x).PosDef := by
    have hh := (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)).add_posSemidef hlo
    simpa only [add_sub_cancel] using hh
  have hbound := hb (fun j => iteratedFDeriv ℝ j.val H x) hjet hlo
  rw [finiteNegativeScalarJet_native hH (Complex.pos_iff.mp hpos.det_pos).1,
    Real.norm_eq_abs, abs_neg] at hbound
  exact hbound

end Yau.NodeProofs.F01Aux
