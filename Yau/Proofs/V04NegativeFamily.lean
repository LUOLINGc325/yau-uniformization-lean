import Yau.Proofs.V04FejerDeformation
import Yau.Proofs.V04NegativeFejerTrace
import Yau.Proofs.V04NegativeErrorLimits
import Yau.Proofs.V04SequenceTails

/-! One common tail enforces all compact-center and energy requirements
before applying the actual Fejer deformation tests. The frequency is
chosen before the sequence index and all errors remain in the original
sequential-then-epsilon order. -/

open Filter
open scoped Matrix Topology ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem negative_family_upper {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} (ha : 4 ≤ a) {C CE M : ℝ} (hC : 0 ≤ C) (hCE : 0 ≤ CE) (hM : 0 ≤ M)
    (hdef : DeformationEstimateWith d j a C CE)
    (hfejer : ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → ∀ P : ℕ, 0 < P →
        negativeFejerError d j a F E P ≤ C * (1 + (variationEnergy d j F).toReal) / P ∧
        ∀ i, HolomorphicColumn (fejerTestColumn d j a F E P i) ∧
          fejerTestColumn d j a F E P i 0 = 0 ∧
          (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
            ∑ r, ‖fejerTestColumn d j a F E P i z r‖ ^ 2 ≤ C ^ 2) ∧
          boundaryDSq (fun θ => fejerTestColumn d j a F E P i (circlePoint θ)) ≤
            ENNReal.ofReal (C * (P + 1)))
    (hsymbol : ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian ∧
        rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤ M)
    (Kc : Set (CotangentCoord n × ℝ)) (hKc : IsCompact Kc)
    (hKint : Kc ⊆ interior (centerCylinder d))
    (hcenters : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : ℕ → VariationDisc X,
      MinimizingSequence d j ε F → ∀ᶠ ν in atTop,
        InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc)
    (F : ℝ → ℕ → VariationDisc X) (E : ℝ → ℕ → ℂ → CotangentMatrix n)
    (hdata : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε) ∧
      ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν))
    (hzero : EpsSeqZero (fun ε ν => ε * (1 + (variationEnergy d j (F ε ν)).toReal))) :
    ∃ (B : ℝ → ℝ) (P : ℝ → ℕ),
      Tendsto (fun ε => ε * B ε) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧ IntermediateFrequency B P ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), SeqUpperZero (fun ν => negativeTrace d j a (F ε ν) (E ε ν) 3 -
        negativeFamilyError ((2 * n : ℕ) * CE) C (2 * (((2 * n : ℕ) : ℝ) * M) ^ 2) B P ε) := by
  obtain ⟨B, hB, hBlim, hcap, hfreq⟩ := frequencySelection d j F
    (hdata.mono fun _ h => h.1) hzero
  let P : ℝ → ℕ := fun ε => max 1 (Nat.ceil (Real.sqrt (B ε / ε)))
  have hP (ε : ℝ) : 0 < P ε := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine ⟨B, P, hBlim, hfreq, ?_⟩
  filter_upwards [hdata, hcenters, hcap, self_mem_nhdsWithin] with ε hε hcenter henergy hpos
  obtain ⟨N, hNmin, hN⟩ := exists_minimizing_sequence_tail hε.1
    (fun ν => InCotangentTimeChart d.chart ((F ε ν).f 0) (F ε ν).s Kc ∧
      1 + (variationEnergy d j (F ε ν)).toReal ≤ B ε)
    ((hcenter (F ε) hε.1).and henergy)
  have hcols (ν : ℕ) (i : CotangentIndex n) :=
    (hfejer (F ε (ν + N)) (E ε (ν + N)) (hε.1.1 (ν + N)) (hε.2 (ν + N)) (P ε) (hP ε)).2 i
  have hseq := fejer_deformation_sequence_upper hC hCE hpos hdef
    (fun ν => F ε (ν + N)) (fun ν => E ε (ν + N)) hNmin Kc hKc hKint
    (fun ν => (hN ν).1) (fun ν => by have hh := (hN ν).2; linarith only [hh])
    (fun ν => hε.2 (ν + N)) hcols
  apply (seqUpperZero_nat_add_iff _ N).1
  apply seqUpperZero_mono hseq
  intro ν
  have ht := negativeTrace_cube_le_fejer_tests hd ha (hε.1.1 (ν + N)) (hε.2 (ν + N)) hM
    (hsymbol _ _ (hε.1.1 (ν + N)) (hε.2 (ν + N))) (P ε)
  have herr := (hfejer _ _ (hε.1.1 (ν + N)) (hε.2 (ν + N)) (P ε) (hP ε)).1
  have hcapν := (hN ν).2
  have hErr : negativeFejerError d j a (F ε (ν + N)) (E ε (ν + N)) (P ε) ≤
      C * B ε / (P ε : ℝ) := herr.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcapν hC) (by positivity))
  have hSQ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hErr)
    (show 0 ≤ 2 * (((2 * n : ℕ) : ℝ) * M) ^ 2 by positivity)
  have hPen := mul_le_mul_of_nonneg_left (add_le_add_right hcapν (C * (P ε + 1)))
    (show 0 ≤ ((2 * n : ℕ) * CE) * ε from mul_nonneg (mul_nonneg (by positivity) hCE) hpos.le)
  dsimp only [negativeFamilyError]
  linarith only [ht, hSQ, hPen]

end Yau.Blueprint.V04Proof
