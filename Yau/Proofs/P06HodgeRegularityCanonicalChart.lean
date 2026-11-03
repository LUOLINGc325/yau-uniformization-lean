import Yau.Proofs.P06HodgeRegularityRepresentativeSupport

/-! A canonical actual smooth compact chart representative of S_a f.
Existence is proved from the original strong path for every Hilbert f. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeCanonicalChart_exists {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : ℝ) (ha : 0 < a) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (f : L2FormHilbert g μ k) :
    ∃ u : ComplexVector n → ℝ, ContDiff ℝ ∞ u ∧ tsupport u ⊆ tsupport χ ∧
      u =ᵐ[lebesgueC n] (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap
        (hodgeHeatHilbert g μ hμ k a f) : ComplexVector n → ℝ) := by
  letI : (lebesgueC n).IsOpenPosMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  obtain ⟨A,hA,hAr⟩ := l2FormHilbert_exists_section g μ (hodgeHeatHilbert g μ hμ k a f)
  have hr : realizeActualForm g μ A hA = hodgeHeatHilbert g μ hμ k a f := hAr
  obtain ⟨u,hu,hAE⟩ := hodgeStrongPath_cutoff_smooth_representative g μ hμ
    (fun t => hodgeHeatHilbert g μ hμ k t f) (hodgeHeatHilbert_strongPath g μ hμ k f)
    ha A hA hr x b χ hχ hcχ hχO c
  have hPAE := chartProjection_actual_ae g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap A hA
  rw [hr] at hPAE
  have hp : (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap
      (hodgeHeatHilbert g μ hμ k a f) : ComplexVector n → ℝ) =ᵐ[lebesgueC n]
      (fun z => χ z * hodgeRegularityCoord b A x z c) := by
    filter_upwards [hPAE] with z hz
    simpa only [chartFunctional,hodgeRegularityCoord,
      LinearMap.coe_toContinuousLinearMap',Basis.coord_apply] using hz
  exact ⟨u,hu,regularityContinuous_tsupport_subset_of_ae (lebesgueC n) hu.continuous hAE
    (isClosed_tsupport χ) tsupport_mul_subset_left,hAE.trans hp.symm⟩

def hodgeCanonicalChart {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : ℝ) (ha : 0 < a) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (f : L2FormHilbert g μ k) : ComplexVector n → ℝ :=
  (hodgeCanonicalChart_exists g μ hμ a ha x b χ hχ hcχ hχO c f).choose

theorem hodgeCanonicalChart_properties {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (a : ℝ) (ha : 0 < a) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (f : L2FormHilbert g μ k) :
    ContDiff ℝ ∞ (hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c f) ∧
      tsupport (hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c f) ⊆ tsupport χ ∧
      hodgeCanonicalChart g μ hμ a ha x b χ hχ hcχ hχO c f =ᵐ[lebesgueC n]
        (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap
          (hodgeHeatHilbert g μ hμ k a f) : ComplexVector n → ℝ) :=
  (hodgeCanonicalChart_exists g μ hμ a ha x b χ hχ hcχ hχO c f).choose_spec

end Yau.NodeProofs.P06Aux
