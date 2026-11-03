import Yau.Proofs.F01SlabWordClockJets
import Yau.Proofs.F01NormalizedWordEquations

/-! The actual smooth positive-time potential has the same complete
spatial word system as the initial extension. Its closed-face clock jets
come from its nonlinear equation, without zero initial data. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem smooth_potential_spatial_word_equations
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ) (b : Space n → ℝ)
    (hu : ContDiffOn ℝ ∞ u (cylinder (ball 0 1) (-1) 1))
    (hS : ∀ t ∈ Icc (-1 : ℝ) 1, ContDiffOn ℝ ∞ (fun z => S (z, t)) (ball 0 1))
    (hb : ContDiffOn ℝ ∞ b (ball 0 1))
    (hpos : ∀ p ∈ cylinder (ball 0 1) (-1) 1, (chartPotentialMatrix S u p).PosDef)
    (hJet : ∀ x ∈ ball 0 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun s => u (x, s))
        (Real.log (chartPotentialMatrix S u (x, t)).det.re + b x) (Icc (-1) 1) t)
    (v : Space n) : PotentialSpatialWordEquations S u b v := by
  let P := fun p => Real.log (chartPotentialMatrix S u p).det.re + b p.1
  let w := spatialDerivativeWord [v] u
  let Pw := spatialDerivativeWord [v] P
  let A := fun p => scalarSymbol (chartPotentialMatrix S u p)
  let f := fun p => traceWith (chartPotentialMatrix S u p)
    (fderiv ℝ (fun z => S (z, p.2)) p.1 v) + fderiv ℝ b p.1 v
  have hI := uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)
  have hDense : ∀ t ∈ Icc (-1 : ℝ) 1, t ∈ closure (interior (Icc (-1 : ℝ) 1)) := by
    intro t ht
    rw [interior_Icc, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact ht
  have hUs (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun z => u (z, t)) (ball 0 1) := contDiffOn_space_slice hu ht
  have hHs (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :=
    chartPotentialMatrix_smooth_slice isOpen_ball (hS t ht) (hUs t ht)
  have hAs (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun z => A (z, t)) (ball 0 1) :=
    scalarSymbol_chartPotential_smooth_slice isOpen_ball (hS t ht) (hUs t ht)
      (fun z hz => hpos (z, t) ⟨hz, ht⟩)
  have hws (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun z => w (z, t)) (ball 0 1) :=
    spatialDerivativeWord_smooth_slice isOpen_ball (hUs t ht) [v]
  have hPws (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun z => Pw (z, t)) (ball 0 1) :=
    spatialDerivativeWord_smooth_slice isOpen_ball
      ((positive_frobenius_logdet_contDiffOn (hHs t ht)
        (fun z hz => hpos (z, t) ⟨hz, ht⟩)).add hb) [v]
  have hClock (vs : List (Space n)) : ∀ x ∈ ball 0 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun s => spatialDerivativeWord vs w (x, s))
        (spatialDerivativeWord vs Pw (x, t)) (Icc (-1) 1) t := by
    intro x hx t ht
    rw [← spatialDerivativeWord_append, ← spatialDerivativeWord_append]
    exact slab_spatial_word_time_jet isOpen_ball hI hDense hu hJet (vs ++ [v]) x hx t ht
  have hEq : ∀ p ∈ cylinder (ball 0 1) (-1) 1,
      Pw p - realHessianContractionCLM (A p) (spatialDD w p) = f p := by
    intro p hp
    have hh := potential_log_spatial_derivative (fun z => S (z, p.2))
      (fun z => u (z, p.2)) b isOpen_ball (hS p.2 hp.2) (hUs p.2 hp.2) hb
      (fun z hz => hpos (z, p.2) ⟨hz, hp.2⟩) hp.1 v
    have hTrace : realHessianContractionCLM (A p) (spatialDD w p) =
        traceWith (chartPotentialMatrix S u p) (leviC (fun z => w (z, p.2)) p.1) :=
      realHessianContractionCLM_eq_complex_trace _
        (((hws p.2 hp.2).contDiffAt (isOpen_ball.mem_nhds hp.1)).of_le (by simp))
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
  have hfs (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun z => f (z, t)) (ball 0 1) :=
    scalar_linear_source_smooth_slice isOpen_ball (hAs t ht) (hws t ht) (hPws t ht)
      (fun z hz => hEq (z, t) ⟨hz, ht⟩)
  intro vs
  constructor
  · exact closed_slab_parabolic_C2 isOpen_ball hI
      (slab_spatialDerivativeWord_smooth isOpen_ball hI
        (slab_spatialDerivativeWord_smooth isOpen_ball hI hu [v]) vs)
  · exact iterated_linear_equation_of_word_jets A w Pw f isOpen_ball (by norm_num)
      hAs hws hfs hClock hEq vs

end Yau.NodeProofs.F01Aux
