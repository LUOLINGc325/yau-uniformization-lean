import Yau.Proofs.V03ConjugateTrace
import Yau.Proofs.V03ExponentialBounds

/-! The auxiliary phase is the one from the actual outer candidate, and
its half-order energy is controlled by the original logarithmic energy. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

def outerWallPhase (d : VariationData X q) (j a : ℕ) (f : ℂ → CotangentPoint X.manifold)
    (θ : ℝ) : ℂ := circlePoint ((a : ℝ) * harmonicConjugateTrace (logTrace d j f) θ)

theorem outerWallPhase_norm (d : VariationData X q) (j a : ℕ)
    (f : ℂ → CotangentPoint X.manifold) (θ : ℝ) : ‖outerWallPhase d j a f θ‖ = 1 :=
  circlePoint_norm _

theorem outerWallPhase_periodic (d : VariationData X q) (j a : ℕ)
    (f : ℂ → CotangentPoint X.manifold) :
    Function.Periodic (outerWallPhase d j a f) (2 * Real.pi) :=
  fun θ => congrArg (fun s => circlePoint ((a : ℝ) * s))
    (harmonicConjugateTrace_periodic (logTrace d j f) θ)

theorem outerWallPhase_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) :
    ContDiff ℝ ∞ (outerWallPhase d j a F.f) :=
  circlePoint_contDiff.comp (contDiff_const.mul
    (harmonicConjugateTrace_contDiff (admissible_logTrace_contDiff hd hF) (logTrace_periodic d j F)))

theorem outerCandidate_eq_wallPower_mul_phase {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) (θ : ℝ) :
    outerCandidate (logTrace d j F.f) a (circlePoint θ) =
      (wallPower d j a (F.f (circlePoint θ)) : ℂ) * outerWallPhase d j a F.f θ := by
  rw [outerCandidate_boundary_factorization (admissible_logTrace_contDiff hd hF)
    (logTrace_periodic d j F)]
  congr 2
  unfold logTrace wallPower
  rw [Real.exp_nat_mul, Real.exp_log (admissible_wallProduct_bounds hd hF θ).1]

theorem outerWallPhase_boundaryDSq_le {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) :
    boundaryDSq (fun θ (_ : Unit) => outerWallPhase d j a F.f θ) ≤
      ENNReal.ofReal ((a : ℝ) ^ 2) * scalarDSq (logTrace d j F.f) := by
  have hq := admissible_logTrace_contDiff hd hF
  have hp := logTrace_periodic d j F
  exact (boundaryDSq_exp_phase_le (harmonicConjugateTrace_contDiff hq hp).continuous
    (harmonicConjugateTrace_periodic _) (a : ℝ)).trans_eq
      (by rw [scalarDSq_harmonicConjugateTrace hq hp])

theorem logTrace_scalarDSq_le_variationEnergy (d : VariationData X q) (j : ℕ) (F : VariationDisc X) :
    scalarDSq (logTrace d j F.f) ≤ variationEnergy d j F := by
  unfold variationEnergy logTrace
  exact le_add_left le_rfl

theorem outerWallPhase_uniform_boundaryDSq_le {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ)
    {E0 : ℝ} (hE0 : 0 ≤ E0) (hE : (variationEnergy d j F).toReal ≤ E0) :
    boundaryDSq (fun θ (_ : Unit) => outerWallPhase d j a F.f θ) ≤
      ENNReal.ofReal ((a : ℝ) ^ 2 * E0) := by
  have hfinite := hF.2.2.2.2.2.2.2.2
  have henergy : variationEnergy d j F ≤ ENNReal.ofReal E0 :=
    (ENNReal.le_ofReal_iff_toReal_le hfinite hE0).mpr hE
  calc
    _ ≤ ENNReal.ofReal ((a : ℝ) ^ 2) * scalarDSq (logTrace d j F.f) :=
      outerWallPhase_boundaryDSq_le hd hF a
    _ ≤ ENNReal.ofReal ((a : ℝ) ^ 2) * ENNReal.ofReal E0 :=
      mul_le_mul le_rfl ((logTrace_scalarDSq_le_variationEnergy d j F).trans henergy) (by positivity) (by positivity)
    _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm

end Yau.Blueprint.V02WallTaylorProof
