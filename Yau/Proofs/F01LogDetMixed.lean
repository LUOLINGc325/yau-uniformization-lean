import Yau.Proofs.F01LogDetWirtinger
import Yau.Proofs.F01InverseBarJet

/-! The full actual mixed log-determinant derivative, including the
negative inverse-matrix product which becomes the squared first-jet term. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix ComplexOrder Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem wirtBar_matrix_trace
    (A : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) (z v : ComplexVector n)
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z) :
    wirtBar (fun w => Matrix.trace (A w)) z v = Matrix.trace (matrixBarJet A z v) := by
  change wirtBar (fun w => ∑ i, A w i i) z v = ∑ i, wirtBar (fun w => A w i i) z v
  exact L14Aux.wirtBar_sum_fun Finset.univ (fun i w => A w i i) z v (fun i _ => hA i i)

theorem logdet_mixed_inverse_trace
    (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) {S : Set (ComplexVector n)}
    (hS : IsOpen S) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => H w i j) S)
    (hpos : ∀ w ∈ S, (H w).PosDef) {z : ComplexVector n} (hz : z ∈ S)
    (v w : ComplexVector n) :
    wirt (fun y => wirtBar (fun x => (Real.log (H x).det.re : ℂ)) y w) z v =
      Matrix.trace ((H z)⁻¹ * matrixBarJet (fun y => matrixUnbarJet H y v) z w -
        (H z)⁻¹ * matrixBarJet H z w * (H z)⁻¹ * matrixUnbarJet H z v) := by
  have hwhole : ContDiffOn ℝ ∞ (fun y => fun i j : Fin n => H y i j) S :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (hH i))
  have hdet (y : ComplexVector n) (hy : y ∈ S) : (H y).det ≠ 0 :=
    ((hpos y hy).isUnit.map Matrix.detMonoidHom).ne_zero
  have hInv (i j : Fin n) : ContDiffOn ℝ ∞ (fun y => (H y)⁻¹ i j) S :=
    L12Aux.contDiffOn_matrix_inv hH hdet i j
  have hU (i j : Fin n) : ContDiffOn ℝ ∞ (fun y => matrixUnbarJet H y v i j) S :=
    L14Aux.wirt_contDiffOn hS _ (hH i j) v
  have hId (i j : Fin n) := ((hInv i j).contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hUd (i j : Fin n) := ((hU i j).contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hProd (i j : Fin n) : DifferentiableAt ℝ
      (fun y => ((H y)⁻¹ * matrixUnbarJet H y v) i j) z := by
    change DifferentiableAt ℝ (fun y => ∑ k, (H y)⁻¹ i k * matrixUnbarJet H y v k j) z
    exact DifferentiableAt.fun_sum (u := Finset.univ) (fun k _ => (hId i k).mul (hUd k j))
  have hlogR : ContDiffOn ℝ ∞ (fun y => Real.log (H y).det.re) S :=
    (Complex.reCLM.contDiff.comp_contDiffOn
      (L12Aux.contDiffOn_matrix_det hH)).log (fun y hy => (Complex.pos_iff.mp (hpos y hy).det_pos).1.ne')
  have hlogC : ContDiffOn ℝ ∞ (fun y => (Real.log (H y).det.re : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hlogR
  have hgerm : (fun y => wirt (fun x => (Real.log (H x).det.re : ℂ)) y v) =ᶠ[𝓝 z]
      (fun y => Matrix.trace ((H y)⁻¹ * matrixUnbarJet H y v)) := by
    filter_upwards [hS.mem_nhds hz] with y hy
    exact logdet_wirt_trace H hS hy v
      ((hwhole.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp)) hpos
  rw [L14Aux.wirt_wirtBar_comm _ z
      ((hlogC.contDiffAt (hS.mem_nhds hz)).of_le (by simp)) w v,
    wirtBar_eq_of_eventuallyEq hgerm, wirtBar_matrix_trace _ z w hProd,
    matrixBarJet_mul (fun y => (H y)⁻¹) (fun y => matrixUnbarJet H y v) z w hId hUd,
    matrixBarJet_inverse H hS hH hdet hz w]
  congr 1
  noncomm_ring

end Yau.NodeProofs.F01Aux
