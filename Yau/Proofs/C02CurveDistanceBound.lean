import Yau.LeafProofs.L12GlobalGeodesic

/-! Distance is bounded by an actual smooth path whose physical speed is
bounded on the indicated closed time interval. -/

noncomputable section
open MeasureTheory Set
open scoped Manifold ENNReal ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem inducedDistance_le_of_path_speed_bound (g : SmoothMetric M)
    (β : ℝ → M.Carrier) (t L : ℝ) (ht : 0 ≤ t) (hL : 0 ≤ L) :
    letI := manifold_realSmooth M
    letI : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
      fun x => underlyingRealTangentNormedAddCommGroup g.form x
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞ β →
      (∀ s ∈ Icc 0 t, ‖realCurveVelocity β s‖ ≤ L) →
      inducedDistance g.form (β 0) (β t) ≤ L * t := by
  let := manifold_realSmooth M
  let : ∀ x : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup g.form x
  let : ∀ x : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentInnerProductSpace g.form x
  intro hβ hspeed
  have hd : ENNReal.ofReal (inducedDistance g.form (β 0) (β t)) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 t := by
    rw [inducedDistance_eq_riemannianEDist g]
    exact Manifold.riemannianEDist_le_pathELength
      (hβ.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).contMDiffOn rfl rfl ht
  have hlen : Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 t ≤
      ENNReal.ofReal (L * t) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    calc
      _ ≤ ∫⁻ _ in Icc (0 : ℝ) t, ENNReal.ofReal L := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        change ‖realCurveVelocity β s‖ₑ ≤ _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hspeed s hs)
      _ = ENNReal.ofReal (L * t) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          sub_zero, ENNReal.ofReal_mul hL]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL ht)).mp (hd.trans hlen)

end Yau.Blueprint.C02Proof
