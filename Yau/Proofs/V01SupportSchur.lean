import Yau.Proofs.V01LocalizedCandidates
import Yau.Proofs.V01TestLevi
import Yau.Proofs.V01OrderedSchur
import Yau.Proofs.V01SupportClock
import Yau.Proofs.V01ExtendedMinimizers
import Yau.Proofs.V03LeviMatrix

/-! The full inner argument for one genuine quadratic support produces the
actual closed Schur witness. No inverse or full-majorant bounds are used. -/

noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff Matrix ComplexOrder MatrixOrder
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem quadratic_support_schur_witness
    (d : VariationData X q) (k : ClockData X) (a : ℕ)
    (hSchur : SymplecticSchur n) (hD05 : DiscFramesContract X.manifold)
    (hG : CotangentImmersion d.G) (hContact : StrictEnvelopeContact d)
    (hReg : InitialDiscRegularization d) (hLoc : LocalizationEstimates d)
    (hCenter : CenterMajorants d a) (hNegative : NegativePartEstimates d a)
    (hSpec : SpectralFactorEstimates d a) (hClock : ClockEstimates d k a)
    (hReplacement : PositiveReplacement d k a) (hSub : SymplecticSubmean d k a)
    {φ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (p : ComplexVector n × ComplexVector n × ℝ) (hφ : ContDiffAt ℝ 2 φ p)
    (α : ℝ) (hα : 0 < α)
    (hTest : d.test = chartTest d.chart (canonicalQuadraticSupport φ p α))
    (hPoint : contactAssoc d.contact = p)
    (hC : (leviMatrix (fun z : CotangentCoord n => φ (z.1, z.2, p.2.2))
      (p.1, p.2.1) cotangentDir - (α : ℂ) • (1 : CotangentMatrix n)).toBlocks₂₂.PosDef) :
    let W := leviMatrix (fun z : CotangentCoord n => φ (z.1, z.2, p.2.2))
      (p.1, p.2.1) cotangentDir - (α : ℂ) • (1 : CotangentMatrix n)
    ∃ K : Herm n, K.PosSemidef ∧ (K - schurComplement W).PosSemidef ∧
      (W.toBlocks₂₂ᵀ * K).trace.re ≤ coordinateTimeSlope φ p := by
  let W : CotangentMatrix n :=
    leviMatrix (fun z : CotangentCoord n => φ (z.1, z.2, p.2.2))
      (p.1, p.2.1) cotangentDir - (α : ℂ) • (1 : CotangentMatrix n)
  have hSlice : ContDiffAt ℝ 2 (fun z : CotangentCoord n => φ (z.1, z.2, p.2.2))
      (p.1, p.2.1) :=
    hφ.comp (p.1, p.2.1) ((spatialAffine_contDiff p.2.2).contDiffAt.of_le (by norm_num))
  have hW : W.IsHermitian :=
    (Yau.Blueprint.V03Proof.leviMatrix_isHermitian hSlice cotangentDir).sub
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.of_nonneg (by exact_mod_cast hα.le)))
  obtain ⟨F, E, hMin, hMaster⟩ :=
    exists_master_minimizers_and_frames d hG hD05 hReg hLoc
  have hFrames : ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      MinimizingSequence d j ε (F j ε) ∧
        ∀ ν, NormalizedDiscFrame d.G (F j ε ν).f (E j ε ν) :=
    hMaster.mono (fun _ hj => hj.mono (fun _ h => ⟨h.1, fun ν => (h.2 ν).2⟩))
  have hTime := localized_support_time_slope d hφ α hTest hPoint F hMin hLoc
  apply schur_witness_of_ordered_majorants hSchur W (coordinateTimeSlope φ p) hW hC
  intro β hβ
  have hCandidates := localized_positive_majorants d k a hContact hLoc hCenter
    hNegative hSpec hClock hReplacement hSub F E hMin hFrames _ hTime β hβ
  filter_upwards [hCandidates, hMin] with j hj hMinj
  filter_upwards [hj] with δ hδ
  filter_upwards [hδ, hMinj] with ε hε hMinε
  filter_upwards [hε] with ν hν
  obtain ⟨A, hA, hAW, hCost⟩ := hν
  have hz : cotangentChart d.chart ((F j ε ν).f 0) ∈ cotangentTarget d.chart :=
    Yau.Blueprint.V03Proof.cotangentChart_mapsTo d.chart
      (admissible_center_in_chart (hMinε.1 ν)).1
  rw [hTest, canonicalChartTest_spatialLevi d.chart p hφ α hz] at hAW
  exact ⟨A, hA, hAW, hCost⟩

end Yau.Blueprint.V01Proof
