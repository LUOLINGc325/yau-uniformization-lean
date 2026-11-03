import Yau.Proofs.F01ZeroExtendedSpatialLinearization
import Yau.Proofs.F01WordJetCommutator
import Yau.Proofs.F01CommutatorSourceHolder

/-! Every spatial word of the first differentiated zero-extended
potential has the genuine C2 regularity and exact linear equation on
the whole initial cylinder. No joint higher-time extension is used. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem chartPotentialMatrix_smooth_slice
    {S : Point n → Matrix (Fin n) (Fin n) ℂ} {V : Point n → ℝ}
    {O : Set (Space n)} {t : ℝ} (hO : IsOpen O)
    (hS : ContDiffOn ℝ ∞ (fun z => S (z, t)) O)
    (hV : ContDiffOn ℝ ∞ (fun z => V (z, t)) O) :
    ContDiffOn ℝ ∞ (fun z => chartPotentialMatrix S V (z, t)) O := by
  have hL : ContDiffOn ℝ ∞ (fun z => leviC (fun y => V (y, t)) z) O :=
    native_levi_frobenius_contDiffOn (q := fun y => V (y, t)) hO hV
  change ContDiffOn ℝ ∞ (fun z => S (z, t) + leviC (fun y => V (y, t)) z) O
  exact hS.add hL

theorem scalarSymbol_chartPotential_smooth_slice
    {S : Point n → Matrix (Fin n) (Fin n) ℂ} {V : Point n → ℝ}
    {O : Set (Space n)} {t : ℝ} (hO : IsOpen O)
    (hS : ContDiffOn ℝ ∞ (fun z => S (z, t)) O)
    (hV : ContDiffOn ℝ ∞ (fun z => V (z, t)) O)
    (hpos : ∀ z ∈ O, (chartPotentialMatrix S V (z, t)).PosDef) :
    ContDiffOn ℝ ∞ (fun z => scalarSymbol (chartPotentialMatrix S V (z, t))) O := by
  have hH : ContDiffOn ℝ ∞ (fun z => chartPotentialMatrix S V (z, t)) O :=
    chartPotentialMatrix_smooth_slice hO hS hV
  exact scalarSymbol_contDiffOn_nonsingular.comp hH (fun z hz => (hpos z hz).det_pos.ne')

theorem scalar_linear_source_smooth_slice
    {A : Point n → Mat n} {w P f : Point n → ℝ} {O : Set (Space n)} {t : ℝ}
    (hO : IsOpen O) (hA : ContDiffOn ℝ ∞ (fun z => A (z, t)) O)
    (hw : ContDiffOn ℝ ∞ (fun z => w (z, t)) O)
    (hP : ContDiffOn ℝ ∞ (fun z => P (z, t)) O)
    (hEq : ∀ z ∈ O, P (z, t) - realHessianContractionCLM (A (z, t))
      (spatialDD w (z, t)) = f (z, t)) :
    ContDiffOn ℝ ∞ (fun z => f (z, t)) O := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => w (z, t))) O :=
    hw.fderiv_of_isOpen hO (by simp)
  have hDD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (fun z => w (z, t)))) O :=
    hD.fderiv_of_isOpen hO (by simp)
  have hProduct := ((realHessianContractionCLM (n := n)).contDiff.comp_contDiffOn hA).clm_apply hDD
  apply (hP.sub hProduct).congr
  intro z hz
  exact (hEq z hz).symm

theorem zero_extended_potential_word_equations
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
    (v : Space n) :
    let V := forwardZeroSpaceTime u
    let w := spatialDerivativeWord [v] V
    let A := fun p => scalarSymbol (chartPotentialMatrix S V p)
    let f := fun p => traceWith (chartPotentialMatrix S V p)
      (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ b p.1 v
    ∀ vs : List (Space n), C2 (O ×ˢ Icc a T) (spatialDerivativeWord vs w) ∧
      ∀ p ∈ O ×ˢ Icc a T, linearOp (O ×ˢ Icc a T) A (fun _ _ => 0)
        (spatialDerivativeWord vs w) p = linearCommutatorSource A w f vs p := by
  dsimp only
  let V := forwardZeroSpaceTime u
  let W := forwardZeroSpaceTime P
  let w := spatialDerivativeWord [v] V
  let Pw := spatialDerivativeWord [v] W
  let A := fun p => scalarSymbol (chartPotentialMatrix S V p)
  let f := fun p => traceWith (chartPotentialMatrix S V p)
    (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ b p.1 v
  have hVS (t : ℝ) (ht : t ∈ Icc a T) : ContDiffOn ℝ ∞ (fun z => V (z, t)) O :=
    forwardZeroSpaceTime_smooth_slices (fun s hs => contDiffOn_space_slice hu hs) ht.2
  have hHs (t : ℝ) (ht : t ∈ Icc a T) :
      ContDiffOn ℝ ∞ (fun z => chartPotentialMatrix S V (z, t)) O :=
    chartPotentialMatrix_smooth_slice hO (hS t ht) (hVS t ht)
  have hAs (t : ℝ) (ht : t ∈ Icc a T) : ContDiffOn ℝ ∞ (fun z => A (z, t)) O := by
    exact scalarSymbol_chartPotential_smooth_slice hO (hS t ht) (hVS t ht)
      (fun z hz => hpos (z, t) ⟨hz, ht⟩)
  have hws (t : ℝ) (ht : t ∈ Icc a T) : ContDiffOn ℝ ∞ (fun z => w (z, t)) O :=
    spatialDerivativeWord_smooth_slice hO (hVS t ht) [v]
  have hClock : ∀ vs : List (Space n), ∀ x ∈ O, ∀ t ∈ Icc a T,
      HasDerivWithinAt (fun s => spatialDerivativeWord vs w (x, s))
        (spatialDerivativeWord vs Pw (x, t)) (Icc a T) t := by
    intro vs x hx t ht
    have hj := zero_extended_spatial_words_time_jet hO hT hu hu0 hP0 hJet (vs ++ [v]) hx ht
    change HasDerivWithinAt (fun s => spatialDerivativeWord vs
      (spatialDerivativeWord [v] (forwardZeroSpaceTime u)) (x, s))
      (spatialDerivativeWord vs (spatialDerivativeWord [v] (forwardZeroSpaceTime P)) (x, t))
      (Icc a T) t
    rw [← spatialDerivativeWord_append, ← spatialDerivativeWord_append]
    exact hj
  have hEq : ∀ p ∈ O ×ˢ Icc a T,
      Pw p - realHessianContractionCLM (A p) (spatialDD w p) = f p := by
    intro p hp
    have hh := zero_extended_potential_spatial_linear_equation S u P b hO hT haT
      hu hu0 hP0 hJet hS hb hpos hLog v hp
    have hSet : {s : ℝ | (p.1, s) ∈ O ×ˢ Icc a T} = Icc a T := by
      ext s
      exact and_iff_right hp.1
    have hTime : timeD (O ×ˢ Icc a T) w p = Pw p := by
      simpa only [timeD, hSet, spatialDerivativeWord] using
        (hClock [] p.1 hp.1 p.2 hp.2).derivWithin (uniqueDiffOn_Icc haT p.2 hp.2)
    rw [linearOp_zero_drift_eq_contraction, hTime] at hh
    exact hh
  have hPws (t : ℝ) (ht : t ∈ Icc a T) : ContDiffOn ℝ ∞ (fun z => Pw (z, t)) O := by
    have hLogS := (positive_frobenius_logdet_contDiffOn (hHs t ht)
      (fun z hz => hpos (z, t) ⟨hz, ht⟩)).add hb
    have hWs : ContDiffOn ℝ ∞ (fun z => W (z, t)) O := by
      apply hLogS.congr
      intro z hz
      exact hLog (z, t) ⟨hz, ht⟩
    exact spatialDerivativeWord_smooth_slice hO hWs [v]
  have hfs (t : ℝ) (ht : t ∈ Icc a T) : ContDiffOn ℝ ∞ (fun z => f (z, t)) O := by
    exact scalar_linear_source_smooth_slice hO (hAs t ht) (hws t ht) (hPws t ht)
      (fun z hz => hEq (z, t) ⟨hz, ht⟩)
  intro vs
  constructor
  · have he : spatialDerivativeWord vs w =
        forwardZeroSpaceTime (spatialDerivativeWord (vs ++ [v]) u) := by
      change spatialDerivativeWord vs (spatialDerivativeWord [v] (forwardZeroSpaceTime u)) = _
      rw [← spatialDerivativeWord_append, spatialDerivativeWord_forwardZeroSpaceTime]
    rw [he]
    exact spatialDerivativeWord_zeroExtension_C2 hO hT haT hu hu0 hP0 hJet (vs ++ [v])
  · exact iterated_linear_equation_of_word_jets A w Pw f hO haT hAs hws hfs hClock hEq vs

end Yau.NodeProofs.F01Aux
