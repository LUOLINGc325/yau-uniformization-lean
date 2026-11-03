import Yau.Proofs.F01CurveLogDetSecond
import Yau.Proofs.F01TraceSquare
import Yau.Proofs.F01ClosedTimeDerivative
import Yau.Proofs.F01LeviTimeCommutation
import Yau.LeafProofs.L22LeviBasic

/-! Differentiating the actual matrix potential evolution gives the
scalar-time heat equation with its full nonpositive Ricci-square source. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

def localMatrixLogDet (H : ComplexVector n × ℝ → Matrix (Fin n) (Fin n) ℂ)
    (p : ComplexVector n × ℝ) : ℝ := Real.log (H p).det.re

def localMatrixLogDetTime (H : ComplexVector n × ℝ → Matrix (Fin n) (Fin n) ℂ)
    (p : ComplexVector n × ℝ) : ℝ := deriv (fun s => localMatrixLogDet H (p.1, s)) p.2

theorem localMatrixLogDet_smooth
    (H : ComplexVector n × ℝ → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} {I : Set ℝ}
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) (S ×ˢ I))
    (hpos : ∀ p ∈ S ×ˢ I, (H p).PosDef) :
    ContDiffOn ℝ ∞ (localMatrixLogDet H) (S ×ˢ I) :=
  (Complex.reCLM.contDiff.comp_contDiffOn (L12Aux.contDiffOn_matrix_det hH)).log
    (fun p hp => (Complex.pos_iff.mp (hpos p hp).det_pos).1.ne')

theorem localMatrixLogDetTime_smooth
    (H : ComplexVector n × ℝ → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) (S ×ˢ I))
    (hpos : ∀ p ∈ S ×ˢ I, (H p).PosDef) :
    ContDiffOn ℝ ∞ (localMatrixLogDetTime H) (S ×ˢ I) := by
  apply (closed_slab_time_derivWithin_smooth hS hI.uniqueDiffOn
    (localMatrixLogDet_smooth H hH hpos)).congr
  intro p hp
  exact (derivWithin_of_isOpen hI hp.2).symm

theorem local_logdet_time_heat_nonpos
    (H : ComplexVector n × ℝ → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) (S ×ˢ I))
    (hpos : ∀ p ∈ S ×ˢ I, (H p).PosDef)
    (hPDE : ∀ z ∈ S, ∀ s ∈ I, ∀ i j,
      HasDerivAt (fun r => H (z, r) i j)
        (leviC (fun w => localMatrixLogDet H (w, s)) z i j) s)
    {z : ComplexVector n} (hz : z ∈ S) {t : ℝ} (ht : t ∈ I) :
    deriv (fun s => localMatrixLogDetTime H (z, s)) t -
      traceWith (H (z, t)) (leviC (fun w => localMatrixLogDetTime H (w, t)) z) ≤ 0 := by
  have hL := localMatrixLogDet_smooth H hH hpos
  have hCurve (i j : Fin n) : ContDiffOn ℝ ∞ (fun s => H (z, s) i j) I :=
    (hH i j).comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨hz, hs⟩)
  have hjet (s : ℝ) (hs : s ∈ I) :
      matrixCurveJet (fun r => H (z, r)) s =
        leviC (fun w => localMatrixLogDet H (w, s)) z := by
    ext i j
    exact (hPDE z hz s hs i j).deriv
  have hjet2 : matrixCurveJet (matrixCurveJet (fun r => H (z, r))) t =
      leviC (fun w => localMatrixLogDetTime H (w, t)) z := by
    ext i j
    have heq : (fun s => matrixCurveJet (fun r => H (z, r)) s i j) =ᶠ[𝓝 t]
        (fun s => leviC (fun w => localMatrixLogDet H (w, s)) z i j) := by
      filter_upwards [hI.mem_nhds ht] with s hs
      exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) (hjet s hs)
    change deriv _ t = _
    rw [heq.deriv_eq, leviC_time_derivative_commute (localMatrixLogDet H) hS hI hL hz ht i j]
    rfl
  have hsecond := logdet_curve_second_derivative (fun r => H (z, r)) hI hCurve
    (fun s hs => hpos (z, s) ⟨hz, hs⟩) ht
  rw [hjet2] at hsecond
  have hspace : ContDiffAt ℝ 2 (fun w => localMatrixLogDet H (w, t)) z :=
    ((hL.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun w hw => ⟨hw, ht⟩)).contDiffAt (hS.mem_nhds hz)).of_le (by simp)
  have hsquare := inverse_metric_trace_square_nonneg (hpos (z, t) ⟨hz, ht⟩)
    (L22Aux.leviC_isHermitian hspace)
  rw [← hjet t ht] at hsquare
  change deriv (deriv (fun r => Real.log (H (z, r)).det.re)) t - _ ≤ 0
  linarith

end Yau.NodeProofs.F01Aux
