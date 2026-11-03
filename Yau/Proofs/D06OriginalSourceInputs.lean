import Yau.Proofs.D06SmoothCircleSobolev
import Yau.Proofs.D06HardyCanonicalBoundary
import Yau.Proofs.D06HardyWeightedSummability

/-! Exact original source inputs, packaged without adding hypotheses. The
matrices below retain the original weighted Hardy factors and Fourier traces. -/

open scoped ComplexOrder ContDiff Matrix
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

structure BoundarySource (r : ℕ) where
  L : ℝ → Matrix (Fin r) (Fin r) ℂ
  m : ℝ
  M : ℝ
  m_pos : 0 < m
  m_le_M : m ≤ M
  smooth : ∀ i j, ContDiff ℝ ∞ (fun t => L t i j)
  periodic : Function.Periodic L (2 * Real.pi)
  order : ∀ t, (L t - (m : ℂ) • 1).PosSemidef ∧ ((M : ℂ) • 1 - L t).PosSemidef

def boundarySourceEval {r : ℕ} (A : Matrix (Fin r) (Fin r) CircleL2) (t : HardyCircle) :
    Matrix (Fin r) (Fin r) ℂ := fun i j => A i j t

namespace BoundarySource
variable {r : ℕ} (s : BoundarySource r)

def symbol : HardyCircle → Matrix (Fin r) (Fin r) ℂ := periodicSymbol s.L s.periodic

theorem symbol_continuous : Continuous s.symbol :=
  periodicSymbol_continuous_of_smooth s.L s.periodic s.smooth

def symbolLp : ∀ i j, MemLp (fun t => s.symbol t i j) ⊤ hardyCircleMeasure :=
  circleMatrix_entries_memLp_top s.symbol s.symbol_continuous

def lower : ∀ t, (s.symbol t - (s.m : ℂ) • 1).PosSemidef :=
  fun t => (periodicSymbol_order s.L s.periodic s.m s.M s.order t).1

def upper : ∀ t, ((s.M : ℂ) • 1 - s.symbol t).PosSemidef :=
  fun t => (periodicSymbol_order s.L s.periodic s.m s.M s.order t).2

def hermitian : ∀ t, (s.symbol t).IsHermitian := fun t => hermitian_of_scalar_lower _ s.m (s.lower t)

theorem M_nonneg : 0 ≤ s.M := s.m_pos.le.trans s.m_le_M

def pColumns : Fin r → HardySeq r :=
  hardyPColumns s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper

def qColumns : Fin r → HardySeq r :=
  hardyQColumns s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper

def H : ℂ → Matrix (Fin r) (Fin r) ℂ :=
  hardyQ s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper

def Hinv : ℂ → Matrix (Fin r) (Fin r) ℂ :=
  hardyP s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower s.M s.M_nonneg s.upper

def hMatrix : Matrix (Fin r) (Fin r) CircleL2 := fun i j => hardyTraceLp (s.qColumns j) i

def pMatrix : Matrix (Fin r) (Fin r) CircleL2 := fun i j => hardyTraceLp (s.pColumns j) i

def lMatrix : Matrix (Fin r) (Fin r) CircleL2 := fun i j =>
  periodicScalarLp (fun t => s.L t i j) (fun t => congrArg (fun A => A i j) (s.periodic t))
    (s.smooth i j).continuous

theorem lMatrix_allSobolev (k : ℕ) (i j : Fin r) : CircleSobolev k (s.lMatrix i j) :=
  periodicScalarLp_sobolev k _ _ (s.smooth i j)

theorem pair_firstSobolev (i j : Fin r) :
    CircleSobolev 1 (s.hMatrix i j) ∧ CircleSobolev 1 (s.pMatrix i j) := by
  have hquad := periodicSymbol_circleDifference_quadratic s.L s.periodic s.smooth
  have hpq := hardyPair_firstSobolev s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower
    s.M s.M_nonneg s.upper hquad j
  exact ⟨hardyTrace_circleSobolev _ 1 hpq.2 i, hardyTrace_circleSobolev _ 1 hpq.1 i⟩

theorem hMatrix_hardy (i j : Fin r) (n : ℤ) (hn : n < 0) : circleCoeff (s.hMatrix i j) n = 0 := by
  rw [circleCoeff_eq_fourierCoeff]
  exact (hardyTrace_fourierCoeff (s.qColumns j) i n).trans (ite_eq_right (by omega))

theorem pMatrix_hardy (i j : Fin r) (n : ℤ) (hn : n < 0) : circleCoeff (s.pMatrix i j) n = 0 := by
  rw [circleCoeff_eq_fourierCoeff]
  exact (hardyTrace_fourierCoeff (s.pColumns j) i n).trans (ite_eq_right (by omega))

theorem lMatrix_trace_ae :
    boundarySourceEval s.lMatrix =ᵐ[hardyCircleMeasure] s.symbol := by
  have hentry (i j : Fin r) : (fun t => s.lMatrix i j t) =ᵐ[hardyCircleMeasure] fun t => s.symbol t i j := by
    have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) hardyCircleMeasure
      (periodicScalarMap (fun t => s.L t i j)
        (fun t => congrArg (fun A => A i j) (s.periodic t)) (s.smooth i j).continuous)
    apply h.trans
    apply Filter.Eventually.of_forall
    intro t
    induction t using Quotient.inductionOn with
    | h t =>
      have hpe : Function.Periodic (fun u => s.L u i j) (2 * Real.pi) :=
        fun u => congrArg (fun A => A i j) (s.periodic u)
      change hpe.lift (t : HardyCircle) = s.symbol (t : HardyCircle) i j
      rw [Function.Periodic.lift_coe, symbol, periodicSymbol_coe]
  have hall := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hentry i))
  filter_upwards [hall] with t ht
  ext i j
  exact ht i j

theorem pair_inverse_ae : ∀ᵐ t ∂hardyCircleMeasure,
    boundarySourceEval s.hMatrix t * boundarySourceEval s.pMatrix t = 1 ∧
      boundarySourceEval s.pMatrix t * boundarySourceEval s.hMatrix t = 1 := by
  filter_upwards [hardyPTrace_inverse s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower
    s.M s.M_nonneg s.upper] with t ht
  exact ⟨ht.2, ht.1⟩

theorem pair_gram_ae : ∀ᵐ t ∂hardyCircleMeasure,
    boundarySourceEval s.lMatrix t = (boundarySourceEval s.hMatrix t)ᴴ * boundarySourceEval s.hMatrix t := by
  filter_upwards [s.lMatrix_trace_ae, hardyQTrace_factor s.symbol s.symbolLp s.hermitian s.m s.m_pos s.lower
    s.M s.M_nonneg s.upper] with t hL ht
  exact hL.trans ht

end BoundarySource
end Yau.NodeProofs.D06Aux
