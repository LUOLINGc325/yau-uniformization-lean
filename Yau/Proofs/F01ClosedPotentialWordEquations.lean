import Yau.Proofs.F01SmoothPotentialWordEquations

/-! The full native word system on the actual closed time interval.
The upper endpoint stays fixed; no future-time values enter its clock
jets, transformed matrix, or iterated linear commutators. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

def PotentialWordEquationsOn (Q : Set (Point n))
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (b : Space n → ℝ) (v : Space n) : Prop :=
  let H := chartPotentialMatrix S u
  let w := spatialDerivativeWord [v] u
  let f := fun p => traceWith (H p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ b p.1 v
  ∀ vs : List (Space n), C2 Q (spatialDerivativeWord vs w) ∧
    ∀ p ∈ Q, linearOp Q (fun q => scalarSymbol (H q)) (fun _ _ => 0)
      (spatialDerivativeWord vs w) p = linearCommutatorSource (fun q => scalarSymbol (H q)) w f vs p

theorem smooth_potential_word_equations_on_closed_interval
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (b : Space n → ℝ)
    {O : Set (Space n)} {l r : ℝ} (hO : IsOpen O) (hlr : l < r)
    (hu : ContDiffOn ℝ ∞ u (cylinder O l r))
    (hS : ∀ t ∈ Icc l r, ContDiffOn ℝ ∞ (fun z => S (z, t)) O)
    (hb : ContDiffOn ℝ ∞ b O)
    (hpos : ∀ p ∈ cylinder O l r, (chartPotentialMatrix S u p).PosDef)
    (hJet : ∀ x ∈ O, ∀ t ∈ Icc l r,
      HasDerivWithinAt (fun s => u (x, s))
        (Real.log (chartPotentialMatrix S u (x, t)).det.re + b x) (Icc l r) t)
    (v : Space n) : PotentialWordEquationsOn (cylinder O l r) S u b v := by
  let P := fun p => Real.log (chartPotentialMatrix S u p).det.re + b p.1
  let w := spatialDerivativeWord [v] u
  let Pw := spatialDerivativeWord [v] P
  let A := fun p => scalarSymbol (chartPotentialMatrix S u p)
  let f := fun p => traceWith (chartPotentialMatrix S u p)
    (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ b p.1 v
  have hI := uniqueDiffOn_Icc hlr
  have hDense : ∀ t ∈ Icc l r, t ∈ closure (interior (Icc l r)) := by
    intro t ht
    rw [interior_Icc, closure_Ioo hlr.ne]
    exact ht
  have hUs (t : ℝ) (ht : t ∈ Icc l r) :
      ContDiffOn ℝ ∞ (fun z => u (z, t)) O := contDiffOn_space_slice hu ht
  have hHs (t : ℝ) (ht : t ∈ Icc l r) :=
    chartPotentialMatrix_smooth_slice hO (hS t ht) (hUs t ht)
  have hAs (t : ℝ) (ht : t ∈ Icc l r) :
      ContDiffOn ℝ ∞ (fun z => A (z, t)) O :=
    scalarSymbol_chartPotential_smooth_slice hO (hS t ht) (hUs t ht)
      (fun z hz => hpos (z, t) ⟨hz, ht⟩)
  have hws (t : ℝ) (ht : t ∈ Icc l r) :
      ContDiffOn ℝ ∞ (fun z => w (z, t)) O :=
    spatialDerivativeWord_smooth_slice hO (hUs t ht) [v]
  have hPws (t : ℝ) (ht : t ∈ Icc l r) :
      ContDiffOn ℝ ∞ (fun z => Pw (z, t)) O :=
    spatialDerivativeWord_smooth_slice hO
      ((positive_frobenius_logdet_contDiffOn (hHs t ht)
        (fun z hz => hpos (z, t) ⟨hz, ht⟩)).add hb) [v]
  have hClock (vs : List (Space n)) : ∀ x ∈ O, ∀ t ∈ Icc l r,
      HasDerivWithinAt (fun s => spatialDerivativeWord vs w (x, s))
        (spatialDerivativeWord vs Pw (x, t)) (Icc l r) t := by
    intro x hx t ht
    rw [← spatialDerivativeWord_append, ← spatialDerivativeWord_append]
    exact slab_spatial_word_time_jet hO hI hDense hu hJet (vs ++ [v]) x hx t ht
  have hEq : ∀ p ∈ cylinder O l r,
      Pw p - realHessianContractionCLM (A p) (spatialDD w p) = f p := by
    intro p hp
    have hh := potential_log_spatial_derivative (fun z => S (z, p.2))
      (fun z => u (z, p.2)) b hO (hS p.2 hp.2) (hUs p.2 hp.2) hb
      (fun z hz => hpos (z, p.2) ⟨hz, hp.2⟩) hp.1 v
    have hTrace : realHessianContractionCLM (A p) (spatialDD w p) =
        traceWith (chartPotentialMatrix S u p) (leviC (fun z => w (z, p.2)) p.1) :=
      realHessianContractionCLM_eq_complex_trace _
        (((hws p.2 hp.2).contDiffAt (hO.mem_nhds hp.1)).of_le (by simp))
    rw [hTrace]
    change fderiv ℝ (fun z => Real.log (chartPotentialMatrix S u (z, p.2)).det.re + b z) p.1 v -
      traceWith (chartPotentialMatrix S u p) (leviC (fun z => w (z, p.2)) p.1) = f p
    change fderiv ℝ (fun z => Real.log (chartPotentialMatrix S u (z, p.2)).det.re + b z) p.1 v =
      traceWith (chartPotentialMatrix S u p)
        (leviC (fun z => fderiv ℝ (fun y => u (y, p.2)) z v) p.1) +
      traceWith (chartPotentialMatrix S u p) (fderiv ℝ (fun z => S (z, p.2)) p.1 v) +
      fderiv ℝ b p.1 v at hh
    dsimp only [w, f, spatialDerivativeWord]
    linarith only [hh]
  have hfs (t : ℝ) (ht : t ∈ Icc l r) :
      ContDiffOn ℝ ∞ (fun z => f (z, t)) O :=
    scalar_linear_source_smooth_slice hO (hAs t ht) (hws t ht) (hPws t ht)
      (fun z hz => hEq (z, t) ⟨hz, ht⟩)
  intro vs
  constructor
  · exact closed_slab_parabolic_C2 hO hI
      (slab_spatialDerivativeWord_smooth hO hI
        (slab_spatialDerivativeWord_smooth hO hI hu [v]) vs)
  · exact iterated_linear_equation_of_word_jets A w Pw f hO hlr
      hAs hws hfs hClock hEq vs


end Yau.NodeProofs.F01Aux
