import Yau.Proofs.V04MajorantSequence
import Yau.Proofs.V04BoundaryAverages
import Yau.Proofs.V04ArbitraryFactorEstimates
import Yau.Proofs.V04SequenceTails

/-! One common finite tail enforces the compact-center and energy caps.
The inverse-factor test direction is free to vary with both limits. -/

open Filter
open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem majorant_family_upper {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} (ha : 4 ≤ a) {δ C CE : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hCE : 0 ≤ CE)
    (hdef : DeformationEstimateWith d j a ((Real.sqrt δ)⁻¹) CE)
    (hbound : ∀ (F : VariationDisc X) (E H Hinv : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      SpectralFactorFor d j a δ F E H Hinv →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Hinv z) ≤ (Real.sqrt δ)⁻¹) ∧
        matrixDSq (fun θ => Hinv (circlePoint θ)) ≤ ENNReal.ofReal C * (1 + variationEnergy d j F))
    (hsymbol : SymbolBounds d a)
    (Kc : Set (CotangentCoord n × ℝ)) (hKc : IsCompact Kc)
    (hKint : Kc ⊆ interior (centerCylinder d))
    (hcenters : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ F : ℕ → VariationDisc X,
      MinimizingSequence d j ε F → ∀ᶠ ν in atTop,
        InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc)
    (F : ℝ → ℕ → VariationDisc X) (E H Hinv : ℝ → ℕ → ℂ → CotangentMatrix n)
    (v : ℝ → ℕ → EuclideanSpace ℂ (CotangentIndex n))
    (hdata : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε) ∧
      ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν) ∧
        SpectralFactorFor d j a δ (F ε ν) (E ε ν) (H ε ν) (Hinv ε ν))
    (hzero : EpsSeqZero (fun ε ν => ε * (1 + (variationEnergy d j (F ε ν)).toReal)))
    (hv : ∀ ε ν, ‖v ε ν‖ ≤ 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), SeqUpperZero (fun ν =>
      outerCenter d j a (F ε ν) ^ 2 * quadValue (centerTestHessian d (F ε ν) (E ε ν))
        (Hinv ε ν 0 *ᵥ WithLp.ofLp (v ε ν)) - 1 -
      (CE * (1 + C)) * ε * (1 + (variationEnergy d j (F ε ν)).toReal)) := by
  obtain ⟨B, _, _, hcap, _⟩ := frequencySelection d j F (hdata.mono fun _ h => h.1) hzero
  obtain ⟨CT, _, hT⟩ := hsymbol j
  filter_upwards [hdata, hcenters, hcap, self_mem_nhdsWithin] with ε hε hcenter henergy hpos
  have hevent := (hcenter (F ε) hε.1).and henergy
  obtain ⟨N, hNmin, hN⟩ := exists_minimizing_sequence_tail hε.1
    (fun ν => InCotangentTimeChart d.chart ((F ε ν).f 0) (F ε ν).s Kc ∧
      1 + (variationEnergy d j (F ε ν)).toReal ≤ B ε) hevent
  have hnorm ν := (hbound _ _ _ _ (hε.1.1 (ν + N)) (hε.2 (ν + N)).1 (hε.2 (ν + N)).2).1
  have hsemi ν := (hbound _ _ _ _ (hε.1.1 (ν + N)) (hε.2 (ν + N)).1 (hε.2 (ν + N)).2).2
  have havg ν := spectralFactor_unit_column_boundary_average hd ha hδ
    (hε.1.1 (ν + N)) (hε.2 (ν + N)).1 (hε.2 (ν + N)).2
    (fun θ => ((hT _ _ (hε.1.1 (ν + N)) (hε.2 (ν + N)).1).1 θ).1)
    (v ε (ν + N)) (hv ε (ν + N))
  have hseq := majorant_sequence_upper hδ hC hCE hpos hdef
    (fun ν => F ε (ν + N)) (fun ν => E ε (ν + N))
    (fun ν => H ε (ν + N)) (fun ν => Hinv ε (ν + N))
    (fun ν => v ε (ν + N)) hNmin Kc hKc hKint
    (fun ν => (hN ν).1) (fun ν => by have hh := (hN ν).2; linarith)
    (fun ν => (hε.2 (ν + N)).1) (fun ν => (hε.2 (ν + N)).2)
    hnorm hsemi (fun ν => hv ε (ν + N)) havg
  exact (seqUpperZero_nat_add_iff _ N).1 hseq

end Yau.Blueprint.V04Proof
