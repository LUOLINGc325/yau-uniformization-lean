import Yau.Proofs.F01FiniteTaylorComposition
import Yau.Proofs.F01ScalarSymbolSmooth

/-! The spatial logdet jet is an actual smooth finite-jet expression
on its positive real-determinant domain. The native identity is the
proved finite Faa di Bruno composition formula. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def complexMatrixLogDet (H : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.log H.det.re

theorem complexMatrixLogDet_contDiffOn :
    ContDiffOn ℝ ∞ (complexMatrixLogDet (n := n)) {H | 0 < H.det.re} := by
  have hRe : ContDiff ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => H.det.re) :=
    Complex.reCLM.contDiff.comp frobenius_matrix_det_contDiff
  exact hRe.contDiffOn.log (fun H hH => hH.ne')

theorem positive_real_determinant_domain_isOpen :
    IsOpen {H : Matrix (Fin n) (Fin n) ℂ | 0 < H.det.re} :=
  isOpen_lt continuous_const (Complex.reCLM.continuous.comp frobenius_matrix_det_contDiff.continuous)

def finiteLogDetSpatialJet (k : ℕ)
    (p : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ :=
  finiteTaylorComposition k
    ((fun j => iteratedFDeriv ℝ j.val complexMatrixLogDet ((p ⟨0, by omega⟩).curry0)), p)

theorem finiteLogDetSpatialJet_contDiffOn (k : ℕ) :
    ContDiffOn ℝ ∞ (finiteLogDetSpatialJet (n := n) k)
      {p | 0 < ((p ⟨0, by omega⟩).curry0).det.re} := by
  letI jetGroups : (j : Fin (k + 1)) → NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    fun j => ContinuousMultilinearMap.normedAddCommGroup'
  letI jetSpaces : (j : Fin (k + 1)) → NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    fun j => ContinuousMultilinearMap.normedSpace'
  let V : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k → Matrix (Fin n) (Fin n) ℂ :=
    fun p => (p ⟨0, by omega⟩).curry0
  have hV : ContDiff ℝ ∞ V :=
    (continuousMultilinearCurryFin0 ℝ (Space n) (Matrix (Fin n) (Fin n) ℂ)).contDiff.comp
      (contDiff_apply ℝ
        (fun j : Fin (k + 1) => ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n)
          (Matrix (Fin n) (Fin n) ℂ)) ⟨0, by omega⟩)
  have hOuter (j : Fin (k + 1)) : ContDiffOn ℝ ∞
      (fun p => iteratedFDeriv ℝ j.val complexMatrixLogDet (V p)) {p | 0 < (V p).det.re} := by
    have hJets : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ j.val (complexMatrixLogDet (n := n)))
        {H | 0 < H.det.re} := by
      intro H hH
      exact ((complexMatrixLogDet_contDiffOn.contDiffAt
        (positive_real_determinant_domain_isOpen.mem_nhds hH)).iteratedFDeriv_right (by simp)).contDiffWithinAt
    exact hJets.comp hV.contDiffOn (fun p hp => hp)
  have hInputs : ContDiffOn ℝ ∞
      (fun p : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k =>
        ((fun j : Fin (k + 1) => iteratedFDeriv ℝ j.val complexMatrixLogDet (V p)), p))
      {p | 0 < (V p).det.re} :=
    (contDiffOn_pi.mpr hOuter).prodMk contDiffOn_id
  exact (finiteTaylorComposition_smooth k).comp_contDiffOn hInputs

theorem finiteLogDetSpatialJet_native
    {H : Space n → Matrix (Fin n) (Fin n) ℂ} {x : Space n}
    (hH : ContDiffAt ℝ ∞ H x) (hPos : 0 < (H x).det.re) (k : ℕ) :
    finiteLogDetSpatialJet k (fun j => iteratedFDeriv ℝ j.val H x) =
      iteratedFDeriv ℝ k (fun z => Real.log (H z).det.re) x := by
  have hLog : ContDiffAt ℝ ∞ (complexMatrixLogDet (n := n)) (H x) :=
    complexMatrixLogDet_contDiffOn.contDiffAt (positive_real_determinant_domain_isOpen.mem_nhds hPos)
  exact finiteTaylorComposition_native hH hLog k

end Yau.NodeProofs.F01Aux
