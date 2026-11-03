import Yau.Proofs.F01LeviSpatialCommutation
import Yau.Proofs.F01FrobeniusLogDetDifferential
import Yau.Proofs.F01PositiveLogDetSmooth
import Yau.Proofs.F01ClosedSpatialTimeJet
import Yau.Proofs.F01NativeScalarLinearEquation
import Yau.Proofs.F01ScalarLeviLinearity

/-! Differentiate the actual nonlinear potential equation in a genuine
spatial direction. Its principal coefficient is the canonical symbol of the
same positive transformed matrix, and every forcing term is computed. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

def chartPotentialMatrix (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ)
    (p : Point n) : Matrix (Fin n) (Fin n) ℂ :=
  S p + leviC (fun z => u (z, p.2)) p.1

theorem potential_spatial_direction_linear_equation
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (b : Space n → ℝ)
    {O : Set (Space n)} {T : ℝ} (hO : IsOpen O) (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T))
    (hS : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => S (x, t)) O)
    (hb : ContDiffOn ℝ ∞ b O)
    (hpos : ∀ p ∈ O ×ˢ Icc 0 T, (chartPotentialMatrix S u p).PosDef)
    (hpde : ∀ x ∈ O, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => u (x, s))
        (Real.log (chartPotentialMatrix S u (x, t)).det.re + b x) (Icc 0 T) t)
    (v : Space n) {p : Point n} (hp : p ∈ O ×ˢ Icc 0 T) :
    linearOp (O ×ˢ Icc 0 T) (fun q => scalarSymbol (chartPotentialMatrix S u q)) (fun _ _ => 0)
      (fun q => fderiv ℝ (fun z => u (z, q.2)) q.1 v) p =
      traceWith (chartPotentialMatrix S u p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
        fderiv ℝ b p.1 v := by
  have hI := uniqueDiffOn_Icc hT
  have hUs : ContDiffOn ℝ ∞ (fun z => u (z, p.2)) O := contDiffOn_space_slice hu hp.2
  have hLs := native_levi_frobenius_contDiffOn hO hUs
  have hHs : ContDiffOn ℝ ∞ (fun z => chartPotentialMatrix S u (z, p.2)) O :=
    (hS p.2 hp.2).add hLs
  have hHd : DifferentiableAt ℝ (fun z => chartPotentialMatrix S u (z, p.2)) p.1 :=
    (hHs.contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp)
  have hLog := positive_frobenius_logdet_contDiffOn hHs (fun z hz => hpos (z, p.2) ⟨hz, hp.2⟩)
  have hLogd := (hLog.contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp)
  have hbd := (hb.contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp)
  have hMatrix : fderiv ℝ (fun z => chartPotentialMatrix S u (z, p.2)) p.1 v =
      fderiv ℝ (fun z => S (z, p.2)) p.1 v +
        leviC (fun z => fderiv ℝ (fun w => u (w, p.2)) z v) p.1 := by
    change fderiv ℝ (fun z => S (z, p.2) + leviC (fun w => u (w, p.2)) z) p.1 v = _
    have hSd := ((hS p.2 hp.2).contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp)
    have hLd := (hLs.contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp)
    have hd := hSd.hasFDerivAt.add hLd.hasFDerivAt
    have he := congrArg (fun D : Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ => D v) hd.fderiv
    have hpoint : fderiv ℝ (fun z => S (z, p.2) + leviC (fun w => u (w, p.2)) z) p.1 v =
        fderiv ℝ (fun z => S (z, p.2)) p.1 v + fderiv ℝ (fun z => leviC (fun w => u (w, p.2)) z) p.1 v := by
      convert! he using 1
    exact hpoint.trans (congrArg (fun H : Matrix (Fin n) (Fin n) ℂ =>
      fderiv ℝ (fun z => S (z, p.2)) p.1 v + H) (leviC_spatial_direction_commute hO hUs hp.1 v))
  have hDeriv : fderiv ℝ (fun z => Real.log (chartPotentialMatrix S u (z, p.2)).det.re + b z) p.1 v =
      traceWith (chartPotentialMatrix S u p)
        (leviC (fun z => fderiv ℝ (fun w => u (w, p.2)) z v) p.1) +
      traceWith (chartPotentialMatrix S u p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
      fderiv ℝ b p.1 v := by
    rw [fderiv_fun_add hLogd hbd]
    simp only [add_apply]
    rw [frobenius_logdet_fderiv_trace (fun z => chartPotentialMatrix S u (z, p.2)) p.1 v hHd (hpos p hp),
      hMatrix, traceWith_add]
    ring
  have hj := closed_space_direction_time_jet
    (P := fun q : Point n => Real.log (chartPotentialMatrix S u q).det.re + b q.1)
    hO hT hu hpde hp.1 hp.2 v
  have hTime : timeD (O ×ˢ Icc 0 T)
      (fun q => fderiv ℝ (fun z => u (z, q.2)) q.1 v) p =
      traceWith (chartPotentialMatrix S u p)
        (leviC (fun z => fderiv ℝ (fun w => u (w, p.2)) z v) p.1) +
      traceWith (chartPotentialMatrix S u p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
      fderiv ℝ b p.1 v := by
    have hs : {s : ℝ | (p.1, s) ∈ O ×ˢ Icc 0 T} = Icc 0 T := by
      ext s
      exact and_iff_right hp.1
    unfold timeD
    rw [hs]
    exact (hj.derivWithin (hI p.2 hp.2)).trans hDeriv
  have hG := closed_slab_space_direction_smooth hO hI hu v
  rw [linearOp_scalarSymbol_eq_complex_heat (closed_slab_slice_jets hG hO hp.1 hp.2).1, hTime]
  ring

end Yau.NodeProofs.F01Aux
