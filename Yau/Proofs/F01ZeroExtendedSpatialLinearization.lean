import Yau.Proofs.F01ZeroExtendedSpatialTimeJets
import Yau.Proofs.F01PotentialLogSpatialDerivative

/-! The genuine nonlinear potential equation linearizes on the whole
zero-extended initial cylinder. Actual one-sided positive-time jets are
glued before the spatial log determinant is differentiated. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem zero_extended_potential_spatial_linear_equation
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u P : Point n → ℝ) (b : Space n → ℝ)
    {O : Set (Space n)} {a T : ℝ} (hO : IsOpen O) (hT : 0 < T) (haT : a < T)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Icc 0 T))
    (hu0 : ∀ x ∈ O, u (x, 0) = 0) (hP0 : ∀ x ∈ O, P (x, 0) = 0)
    (hJet : ∀ x ∈ O, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => u (x, s)) (P (x, t)) (Icc 0 T) t)
    (hS : ∀ t ∈ Icc a T, ContDiffOn ℝ ∞ (fun z => S (z, t)) O)
    (hb : ContDiffOn ℝ ∞ b O)
    (hpos : ∀ p ∈ O ×ˢ Icc a T,
      (chartPotentialMatrix S (forwardZeroSpaceTime u) p).PosDef)
    (hLog : ∀ p ∈ O ×ˢ Icc a T, forwardZeroSpaceTime P p =
      Real.log (chartPotentialMatrix S (forwardZeroSpaceTime u) p).det.re + b p.1)
    (v : Space n) {p : Point n} (hp : p ∈ O ×ˢ Icc a T) :
    linearOp (O ×ˢ Icc a T)
      (fun q => scalarSymbol (chartPotentialMatrix S (forwardZeroSpaceTime u) q))
      (fun _ _ => 0) (spatialDerivativeWord [v] (forwardZeroSpaceTime u)) p =
      traceWith (chartPotentialMatrix S (forwardZeroSpaceTime u) p)
        (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ b p.1 v := by
  let V := forwardZeroSpaceTime u
  let W := forwardZeroSpaceTime P
  have hVS : ContDiffOn ℝ ∞ (fun z => V (z, p.2)) O :=
    forwardZeroSpaceTime_smooth_slices (fun t ht => contDiffOn_space_slice hu ht) hp.2.2
  have hj := zero_extended_spatial_words_time_jet hO hT hu hu0 hP0 hJet [v] hp.1 hp.2
  have hSet : {s : ℝ | (p.1, s) ∈ O ×ˢ Icc a T} = Icc a T := by
    ext s
    exact and_iff_right hp.1
  have hTime : timeD (O ×ˢ Icc a T) (spatialDerivativeWord [v] V) p =
      fderiv ℝ (fun z => W (z, p.2)) p.1 v := by
    simpa only [timeD, hSet, spatialDerivativeWord] using
      hj.derivWithin (uniqueDiffOn_Icc haT p.2 hp.2)
  have he : (fun z => W (z, p.2)) =ᶠ[𝓝 p.1]
      (fun z => Real.log (chartPotentialMatrix S V (z, p.2)).det.re + b z) := by
    filter_upwards [hO.mem_nhds hp.1] with z hz
    exact hLog (z, p.2) ⟨hz, hp.2⟩
  have hDeriv := potential_log_spatial_derivative (fun z => S (z, p.2))
    (fun z => V (z, p.2)) b hO (hS p.2 hp.2) hVS hb
    (fun z hz => hpos (z, p.2) ⟨hz, hp.2⟩) hp.1 v
  have hClock : timeD (O ×ˢ Icc a T) (spatialDerivativeWord [v] V) p =
      traceWith (chartPotentialMatrix S V p)
        (leviC (fun z => fderiv ℝ (fun w => V (w, p.2)) z v) p.1) +
      traceWith (chartPotentialMatrix S V p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
      fderiv ℝ b p.1 v := by
    exact hTime.trans ((congrArg (fun D : Space n →L[ℝ] ℝ => D v) he.fderiv_eq).trans hDeriv)
  have hV1 : ContDiffAt ℝ 2
      (fun z => spatialDerivativeWord [v] V (z, p.2)) p.1 :=
    ((spatialDerivativeWord_smooth_slice hO hVS [v]).contDiffAt
      (hO.mem_nhds hp.1)).of_le (by simp)
  change linearOp (O ×ˢ Icc a T) (fun q => scalarSymbol (chartPotentialMatrix S V q))
    (fun _ _ => 0) (spatialDerivativeWord [v] V) p = _
  rw [linearOp_scalarSymbol_eq_complex_heat hV1, hClock]
  dsimp only [spatialDerivativeWord, V]
  ring

end Yau.NodeProofs.F01Aux
