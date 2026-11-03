import Yau.LeafProofs.L14Gauge
import Yau.LeafProofs.L23FieldMetric

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau

variable {n : ℕ} {M : ComplexManifold n}

theorem inducedDistance_function_bound (h : HermitianField M) (hh : MetricSmooth h)
    (F : M.Carrier → ℝ) (hF : SmoothFn F)
    (hD : ∀ (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x),
      |(show ℝ from mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) F x v)| ≤
        Real.sqrt (2 * hermitianNormSq (h x) (LeafProofs.L12Aux.realTangentEquiv x v)))
    (x y : M.Carrier) : |F x - F y| ≤ inducedDistance h x y := by
  letI := LeafProofs.L12Aux.manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => LeafProofs.L12Aux.underlyingRealTangentNormedAddCommGroup h z
  have hFM := LeafProofs.L18Aux.contMDiff_real_of_smoothFn hF
  have hED : ENNReal.ofReal |F x - F y| ≤
      Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y := by
    simp only [Manifold.riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : ℝ → M.Carrier := γ ∘ projIcc 0 1 zero_le_one
    have he : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 e (Icc 0 1) :=
      hγ.comp_contMDiffOn contMDiffOn_projIcc
    have hfe : ContDiffOn ℝ 1 (fun t => F (e t)) (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp ((hFM.of_le (by norm_num)).comp_contMDiffOn he)
    have hend : ENNReal.ofReal |F x - F y| = ‖F (e 1) - F (e 0)‖ₑ := by
      simp [e, Real.enorm_eq_ofReal_abs, abs_sub_comm]
    rw [hend]
    apply (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hfe zero_le_one).trans
    rw [Manifold.lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc,
      Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
    change (∫⁻ t in Icc (0 : ℝ) 1,
      ‖fderivWithin ℝ (fun u => F (e u)) (Icc 0 1) t (1 : ℝ)‖ₑ) ≤
        ∫⁻ t in Icc (0 : ℝ) 1,
          ‖mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) e (Icc 0 1) t (1 : ℝ)‖ₑ
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have huniq : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) t :=
      (uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt
    have hchain := mfderiv_comp_mfderivWithin t
      ((hFM (e t)).mdifferentiableAt (by simp))
      ((he t ht).mdifferentiableWithinAt (by simp)) huniq
    rw [mfderivWithin_eq_fderivWithin] at hchain
    have hval := congrArg (fun L => L (1 : ℝ)) hchain
    change fderivWithin ℝ (fun u => F (e u)) (Icc 0 1) t (1 : ℝ) =
      (show ℝ from mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) F (e t)
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) e (Icc 0 1) t (1 : ℝ))) at hval
    refine (congrArg (fun r : ℝ => ‖r‖ₑ) hval).le.trans ?_
    have hbound := hD (e t)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) e (Icc 0 1) t (1 : ℝ))
    have hnorm := LeafProofs.L12Aux.underlyingRealTangent_norm h (e t)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) e (Icc 0 1) t (1 : ℝ))
    rw [← hnorm] at hbound
    change ‖(show ℝ from mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) F (e t)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) e (Icc 0 1) t (1 : ℝ)))‖ₑ ≤ _
    rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hbound
  rw [← LeafProofs.L23Aux.inducedDistance_eq_riemannianEDist h hh x y] at hED
  exact (ENNReal.ofReal_le_ofReal_iff (LeafProofs.L23Aux.inducedDistance_nonneg h hh x y)).mp hED

end Yau.Proofs.B01Aux
