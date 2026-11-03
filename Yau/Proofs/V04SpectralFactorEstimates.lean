import Yau.Proofs.V04CanonicalFactorBounds
import Yau.Proofs.V04MatrixReindex
import Yau.Proofs.V04MajorantSpectralBounds
import Yau.Proofs.V04BoundaryRegularity
import Yau.Proofs.V03CirclePeriod

/-! The original spectral-factor estimates use one actual canonical D06
pair for the smoothed original symbol. The constant is chosen before the
disc and frame, with the precise closed-disc inverse norm and Fourier
seminorm retained. -/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D06Aux

variable {n q : ℕ} {X : KahlerManifold n}

theorem spectralFactorEstimates_of_symbolBounds {d : VariationData X q}
    (hd : VariationSetup d) {a : ℕ} (ha : 4 ≤ a) (hsymbol : SymbolBounds d a) :
    SpectralFactorEstimates d a := by
  intro j δ hδ
  obtain ⟨C, hC, hbound⟩ := hsymbol j
  let K : ℝ := 1 / (2 * δ ^ 3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * C, mul_nonneg hK hC, fun F E hF hE => ?_⟩
  let T := fun θ => boundarySymbol d j a F E (circlePoint θ)
  let L := fun θ => smoothMajorant δ (T θ)
  let e := cotangentFinEquiv n
  let R := matrixReindexStarAlgEquiv e
  have hT : ∀ θ, (T θ).IsHermitian := fun θ => ((hbound F E hF hE).1 θ).1
  have hTc : ∀ i k, ContDiff ℝ ∞ (fun θ => T θ i k) :=
    boundarySymbol_trace_contDiff hd j a ha F hF E hE
  have hTp : Function.Periodic T (2 * Real.pi) := circleTrace_periodic (boundarySymbol d j a F E)
  have hLower (θ : ℝ) : (R (L θ) - (δ : ℂ) • 1).PosSemidef := by
    simpa only [map_sub, map_smul, map_one] using
      matrixReindex_posSemidef e (smoothMajorant_ge_delta hδ (T θ) (hT θ))
  have hUpper (θ : ℝ) : ((((C + 2 * δ : ℝ) : ℂ) • 1) - R (L θ)).PosSemidef := by
    simpa only [map_sub, map_smul, map_one] using matrixReindex_posSemidef e
      (smoothMajorant_upper_order hδ hC (T θ) (hT θ) (((hbound F E hF hE).1 θ).2))
  let s : BoundarySource (2 * n) :=
    { L := fun θ => R (L θ), m := δ, M := C + 2 * δ,
      m_pos := hδ, m_le_M := by linarith only [hC, hδ],
      smooth := fun i k => smoothMajorant_entry_contDiff hδ T hTc hT (e.symm i) (e.symm k),
      periodic := fun θ => congrArg R (congrArg (smoothMajorant δ) (hTp θ)),
      order := fun θ => ⟨hLower θ, hUpper θ⟩ }
  let H : ℂ → CotangentMatrix n := fun z => R.symm (s.H z)
  let Hinv : ℂ → CotangentMatrix n := fun z => R.symm (s.Hinv z)
  have hc := s.closed_complex_smooth
  have hHc : ContinuousOn s.H (Metric.closedBall 0 1) :=
    continuousOn_pi.2 (fun i => continuousOn_pi.2 (fun k => (hc i k).1.continuousOn))
  have hPc : ContinuousOn s.Hinv (Metric.closedBall 0 1) :=
    continuousOn_pi.2 (fun i => continuousOn_pi.2 (fun k => (hc i k).2.continuousOn))
  have hfactor : SpectralFactorFor d j a δ F E H Hinv := by
    refine ⟨?_, ?_, ?_⟩
    · intro i k
      exact hc (e i) (e k)
    · intro z hz
      have hh := s.closed_inverse hHc hPc z hz
      constructor
      · simpa only [H, Hinv, map_mul, map_one] using congrArg R.symm hh.1
      · simpa only [H, Hinv, map_mul, map_one] using congrArg R.symm hh.2
    · intro θ
      have hh := congrArg R.symm (s.boundary_factor hHc θ)
      change R.symm (R (L θ)) = R.symm ((onCircle s.H θ)ᴴ * onCircle s.H θ) at hh
      simpa only [H, L, T, onCircle, circlePoint, map_mul, ← Matrix.star_eq_conjTranspose,
        map_star, R.symm_apply_apply] using hh.symm
  have hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Hinv z) ≤ (Real.sqrt δ)⁻¹ := by
    intro z hz
    change ‖R.symm (s.Hinv z)‖ ≤ (Real.sqrt δ)⁻¹
    rw [StarAlgEquiv.norm_map]
    exact boundarySource_inverse_closed_bound s z hz
  have hSourceL : matrixDSq s.L = matrixDSq L := matrixDSq_reindex e L
  have hLcap : matrixDSq s.L ≤ ENNReal.ofReal C * (1 + variationEnergy d j F) := by
    rw [hSourceL]
    exact (matrixDSq_smoothMajorant_le hδ hTc hTp hT).trans (hbound F E hF hE).2
  have hSourceH : matrixDSq (fun θ => Hinv (circlePoint θ)) = matrixDSq (onCircle s.Hinv) := by
    change matrixDSq (fun θ => matrixReindexStarAlgEquiv e.symm (onCircle s.Hinv θ)) = _
    exact matrixDSq_reindex e.symm (onCircle s.Hinv)
  refine ⟨H, Hinv, hfactor, hnorm, ?_⟩
  calc
    _ = matrixDSq (onCircle s.Hinv) := hSourceH
    _ ≤ ENNReal.ofReal K * matrixDSq s.L := boundarySource_inverse_matrixDSq s
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal C * (1 + variationEnergy d j F)) :=
      mul_le_mul_of_nonneg_left hLcap bot_le
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hK]

end Yau.Blueprint.V04Proof
