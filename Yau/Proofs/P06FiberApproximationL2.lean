import Yau.Proofs.P06FiberApproximationForms

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.NodeProofs.P06Aux.FiberApprox
open Yau Yau.LeafProofs G04Aux Clip
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem functionalForm_coefficients_measurable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (p : ℕ → Polynomial ℝ) (F : ℝ → ℝ) {R : ℝ}
    (hs : ∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R)
    (ht : TendstoUniformlyOn (fun j x => (p j).eval x) F atTop (Icc (-R) R))
    (b : M.Carrier) (I : Fin 2 → RIdx n) : AEStronglyMeasurable
      (fun y => functionalForm g.form A F y (fun r => chartVec b y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) b).source) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun j => L03.smoothRealForm_coefficient_aestronglyMeasurable μ _
      (FiberPoly.polynomialForm_smooth g A hA h11 (p j)) b I)
  exact Eventually.of_forall (fun y => polynomialForm_evaluation_tendsto g.form A h11 p F hs ht y _)

/-- No measurability of the clipped coefficients is assumed: it follows from smooth approximants. -/
theorem functionalForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A)
    (p : ℕ → Polynomial ℝ) (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h0 : F 0 = 0) {R : ℝ}
    (hs : ∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R)
    (ht : TendstoUniformlyOn (fun j x => (p j).eval x) F atTop (Icc (-R) R)) :
    L2RealForm g.form μ (functionalForm g.form A F) := by
  have hA2 := L03.smooth_compactlySupported_l2RealForm g μ hμ A hA hcA
  refine ⟨functionalForm_coefficients_measurable g μ A hA h11 p F hs ht, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal ?_)) hA2.2
  rw [formNormSq_eq_pointFormHS g.form _ (functionalForm_oneOne g.form A F),
    formNormSq_eq_pointFormHS g.form A h11]
  exact pow_le_pow_left₀ (norm_nonneg _) (functionalForm_pointNorm_le g.form A h11 F hF h0 x) 2

theorem pointFormHS_sub (g : HermitianField M) (A B : RealForm M 2) (x : M.Carrier) :
    pointFormHS g (A - B) x = pointFormHS g A x - pointFormHS g B x := by
  simp only [pointFormHS, formHermitianMatrix_sub, relativeMatrixHS, metricWhiten_sub,
    matrixToHS_sub]

theorem polynomialForm_pointFormHS_tendsto (g : HermitianField M) (A : RealForm M 2)
    (h11 : RealOneOne A) (p : ℕ → Polynomial ℝ) (F : ℝ → ℝ) {R : ℝ}
    (hs : ∀ x i, (whiteHermitian g A h11 x).eigenvalues i ∈ Icc (-R) R)
    (ht : TendstoUniformlyOn (fun j x => (p j).eval x) F atTop (Icc (-R) R))
    (x : M.Carrier) : Tendsto (fun j => pointFormHS g (FiberPoly.polynomialForm g A h11 (p j)) x)
      atTop (𝓝 (pointFormHS g (functionalForm g A F) x)) := by
  simp only [pointFormHS_polynomialForm, pointFormHS_functionalForm]
  have hc : Continuous (matrixToHS (n := n)) := by
    exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
  exact (hc.tendsto _).comp (aeval_tendsto_of_uniform _ (whiteHermitian g A h11 x) p F (hs x) ht)

/-- The original extended-real squared distance converges to zero by genuine dominated convergence. -/
theorem polynomialForm_l2_distance_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (h11 : RealOneOne A)
    (p : ℕ → Polynomial ℝ) (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x i, (whiteHermitian g.form A h11 x).eigenvalues i ∈ Icc (-R) R)
    (hp : ∀ j, (p j).eval 0 = 0)
    (hd : ∀ j x, x ∈ Icc (-R) R → |(p j).derivative.eval x| ≤ 1)
    (ht : TendstoUniformlyOn (fun j x => (p j).eval x) F atTop (Icc (-R) R)) :
    Tendsto (fun j => formL2DistanceSq g.form μ (FiberPoly.polynomialForm g.form A h11 (p j))
      (functionalForm g.form A F)) atTop (𝓝 0) := by
  let B := functionalForm g.form A F
  let P := fun j => FiberPoly.polynomialForm g.form A h11 (p j)
  have hB : L2RealForm g.form μ B := functionalForm_l2 g μ hμ A hA hcA h11 p F hF h0 hs ht
  have hP (j : ℕ) : L2RealForm g.form μ (P j) :=
    FiberPoly.polynomialForm_l2 g μ hμ A hA h11 (p j) (hp j) hcA
  have hD (j : ℕ) := L03.l2RealForm_sub g μ (P j) B (hP j) hB
  have hm (j : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (formNormSq g.form (P j - B) x)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (L03.formNormSq_aestronglyMeasurable g μ _ (hD j)).aemeasurable
  have hb (j : ℕ) : (fun x => ENNReal.ofReal (formNormSq g.form (P j - B) x)) ≤ᵐ[μ]
      (fun x => ENNReal.ofReal (4 * formNormSq g.form A x)) := by
    refine Eventually.of_forall (fun x => ENNReal.ofReal_le_ofReal ?_)
    rw [formNormSq_eq_pointFormHS g.form _
      (realOneOne_sub _ _ (FiberPoly.polynomialForm_oneOne g.form A h11 (p j))
        (functionalForm_oneOne g.form A F)), pointFormHS_sub,
      formNormSq_eq_pointFormHS g.form A h11]
    have hpn := polynomialForm_pointNorm_le g.form A h11 (p j) hR hs (hp j) (hd j) x
    have hbn := functionalForm_pointNorm_le g.form A h11 F hF h0 x
    have htri := (norm_sub_le (pointFormHS g.form (P j) x) (pointFormHS g.form B x)).trans
      (add_le_add hpn hbn)
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith
  have hA2 := L03.smooth_compactlySupported_l2RealForm g μ hμ A hA hcA
  have hbound : (∫⁻ x, ENNReal.ofReal (4 * formNormSq g.form A x) ∂μ) < ⊤ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [lintegral_const_mul' _ _ (by simp)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA2.2
  have hl (x : M.Carrier) : Tendsto (fun j => ENNReal.ofReal (formNormSq g.form (P j - B) x))
      atTop (𝓝 (0 : ENNReal)) := by
    have hvec := (polynomialForm_pointFormHS_tendsto g.form A h11 p F hs ht x).sub_const
      (pointFormHS g.form B x)
    have hnorm : Tendsto (fun j => ‖pointFormHS g.form (P j) x - pointFormHS g.form B x‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [B, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hvec.norm.pow 2
    have he (j : ℕ) : formNormSq g.form (P j - B) x =
        ‖pointFormHS g.form (P j) x - pointFormHS g.form B x‖ ^ 2 := by
      rw [formNormSq_eq_pointFormHS g.form _
        (realOneOne_sub _ _ (FiberPoly.polynomialForm_oneOne g.form A h11 (p j))
          (functionalForm_oneOne g.form A F)), pointFormHS_sub]
    simp_rw [he]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
  have ht' := tendsto_lintegral_of_dominated_convergence'
    (fun x => ENNReal.ofReal (4 * formNormSq g.form A x)) hm hb (ne_of_lt hbound)
    (Eventually.of_forall hl)
  simpa only [formL2DistanceSq, lintegral_zero] using ht'

end Yau.NodeProofs.P06Aux.FiberApprox
