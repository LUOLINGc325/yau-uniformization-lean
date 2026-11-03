import Yau.Proofs.F01MatrixCurveJet
import Yau.Proofs.F01LogDetCurve

/-! The actual second time derivative of log det has its full negative
inverse-matrix square. All matrix jets are literal scalar derivatives. -/
noncomputable section
open Set Filter
open scoped Matrix ContDiff Topology ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem matrixCurve_trace_hasDerivAt (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hH : ∀ i j, DifferentiableAt ℝ (fun s => H s i j) t) :
    HasDerivAt (fun s => Matrix.trace (H s)) (Matrix.trace (matrixCurveJet H t)) t :=
  HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hH i i).hasDerivAt)

theorem logdet_curve_deriv_trace (H : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hH : ∀ i j, DifferentiableAt ℝ (fun s => H s i j) t) (hpos : (H t).PosDef) :
    deriv (fun s => Real.log (H s).det.re) t = traceWith (H t) (matrixCurveJet H t) := by
  have hh := logdet_curve_hasDerivWithinAt H (matrixCurveJet H t)
    (I := univ) (t := t) (fun i j => (hH i j).hasDerivAt.hasDerivWithinAt) hpos
  exact (hh.hasDerivAt (by simp)).deriv

theorem logdet_curve_second_derivative
    (H : ℝ → Matrix (Fin n) (Fin n) ℂ) {I : Set ℝ} (hI : IsOpen I)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun s => H s i j) I)
    (hpos : ∀ s ∈ I, (H s).PosDef) {t : ℝ} (ht : t ∈ I) :
    deriv (deriv (fun s => Real.log (H s).det.re)) t =
      traceWith (H t) (matrixCurveJet (matrixCurveJet H) t) -
        (Matrix.trace ((H t)⁻¹ * matrixCurveJet H t * (H t)⁻¹ * matrixCurveJet H t)).re := by
  have hdet (s : ℝ) (hs : s ∈ I) : (H s).det ≠ 0 :=
    ((hpos s hs).isUnit.map Matrix.detMonoidHom).ne_zero
  have hHd (i j : Fin n) := ((hH i j).contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have hId (i j : Fin n) := ((L12Aux.contDiffOn_matrix_inv hH hdet i j).contDiffAt
    (hI.mem_nhds ht)).differentiableAt (by simp)
  have hD (i j : Fin n) : ContDiffOn ℝ ∞ (fun s => matrixCurveJet H s i j) I :=
    (hH i j).deriv_of_isOpen hI (m := ∞) (by simp)
  have hDd (i j : Fin n) := ((hD i j).contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
  have heq : deriv (fun s => Real.log (H s).det.re) =ᶠ[𝓝 t]
      (fun s => traceWith (H s) (matrixCurveJet H s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact logdet_curve_deriv_trace H s
      (fun i j => ((hH i j).contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)) (hpos s hs)
  rw [heq.deriv_eq]
  have hproduct (i j : Fin n) : DifferentiableAt ℝ
      (fun s => ((H s)⁻¹ * matrixCurveJet H s) i j) t := by
    change DifferentiableAt ℝ (fun s => ∑ k, (H s)⁻¹ i k * matrixCurveJet H s k j) t
    exact DifferentiableAt.fun_sum (u := Finset.univ) (fun k _ => (hId i k).mul (hDd k j))
  have htrace := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (matrixCurve_trace_hasDerivAt (fun s => (H s)⁻¹ * matrixCurveJet H s) t hproduct)
  change HasDerivAt (fun s => (Matrix.trace ((H s)⁻¹ * matrixCurveJet H s)).re)
    (Matrix.trace (matrixCurveJet (fun s => (H s)⁻¹ * matrixCurveJet H s) t)).re t at htrace
  change deriv (fun s => (Matrix.trace ((H s)⁻¹ * matrixCurveJet H s)).re) t = _
  rw [htrace.deriv, matrixCurveJet_mul (fun s => (H s)⁻¹) (matrixCurveJet H) t hId hDd,
    matrixCurveJet_inverse H hI hH hdet ht]
  simp only [Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg, Complex.add_re, Complex.neg_re,
    traceWith]
  ring

end Yau.NodeProofs.F01Aux
