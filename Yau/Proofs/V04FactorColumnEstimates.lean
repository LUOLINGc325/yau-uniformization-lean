import Yau.Proofs.V04FactorColumns
import Yau.Proofs.V04SequenceTails

/-! All quantitative bounds concern the same caller-supplied inverse
factor. Finiteness is established before converting a seminorm to a real. -/

open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem spectralFactor_unit_column_estimates {d : VariationData X q} {j a : ℕ} {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) {F : VariationDisc X}
    {E H Hinv : ℂ → CotangentMatrix n} (hF : AdmissibleVariationDisc d j F)
    (hH : SpectralFactorFor d j a δ F E H Hinv)
    (hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Hinv z) ≤ (Real.sqrt δ)⁻¹)
    (hsemi : matrixDSq (fun θ => Hinv (circlePoint θ)) ≤
      ENNReal.ofReal C * (1 + variationEnergy d j F))
    (v : EuclideanSpace ℂ (CotangentIndex n)) (hv : ‖v‖ ≤ 1) :
    HolomorphicColumn (fun z => Hinv z *ᵥ WithLp.ofLp v) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        ∑ i, ‖(Hinv z *ᵥ WithLp.ofLp v) i‖ ^ 2 ≤ ((Real.sqrt δ)⁻¹) ^ 2) ∧
      boundaryDSq (fun θ => Hinv (circlePoint θ) *ᵥ WithLp.ofLp v) ≠ ⊤ ∧
      boundaryDSq (fun θ => Hinv (circlePoint θ) *ᵥ WithLp.ofLp v) ≤
        ENNReal.ofReal C * (1 + variationEnergy d j F) ∧
      (boundaryDSq (fun θ => Hinv (circlePoint θ) *ᵥ WithLp.ofLp v)).toReal ≤
        C * (1 + (variationEnergy d j F).toReal) := by
  have hcircle (θ : ℝ) : circlePoint θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, circlePoint, Complex.norm_exp]
  have htrace : ∀ i k, Continuous (fun θ => Hinv (circlePoint θ) i k) := by
    intro i k
    exact (hH.1 i k).2.continuousOn.comp_continuous
      (by unfold circlePoint; fun_prop : Continuous circlePoint) hcircle
  have hbound := (boundaryDSq_matrix_unit_column_le _ v hv htrace).trans hsemi
  have he : variationEnergy d j F ≠ ⊤ := admissible_energy_finite hF
  have hfinite : ENNReal.ofReal C * (1 + variationEnergy d j F) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨by simp, he⟩)
  have hbfinite : boundaryDSq (fun θ => Hinv (circlePoint θ) *ᵥ WithLp.ofLp v) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hfinite))
  have hreal := ENNReal.toReal_mono hfinite hbound
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_add (by simp : (1 : ENNReal) ≠ ⊤) he, ENNReal.toReal_one] at hreal
  exact ⟨closedDisc_matrix_column_holomorphic Hinv (fun i k => (hH.1 i k).2) v,
    closedDisc_matrix_unit_column_sup Hinv (inv_nonneg.mpr (Real.sqrt_nonneg δ)) hnorm v hv,
    hbfinite, hbound, hreal⟩

end Yau.Blueprint.V04Proof
