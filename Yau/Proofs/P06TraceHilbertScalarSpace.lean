import Yau.Proofs.P06TraceHilbertAdjoint

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalar_l2 (g : SmoothMetric M) (μ : Measure M.Carrier) (f : Lp ℝ 2 μ) :
    L2RealForm g.form μ (scalarForm f) := by
  refine ⟨fun x I => (Lp.memLp f).aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  have hi := (Lp.memLp f).integrable_sq
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => formNormSq_nonneg g.form (scalarForm f) x))).mp
  change HasFiniteIntegral (fun x => formNormSq g.form (scalarForm f) x) μ
  simpa only [scalarForm_normSq] using hi.2

def scalarValue (g : SmoothMetric M) (μ : Measure M.Carrier) (f : Lp ℝ 2 μ) :
    L2FormHilbert g μ 0 := realizeActualForm g μ (scalarForm f) (scalar_l2 g μ f)

theorem scalarValue_inner (g : SmoothMetric M) (μ : Measure M.Carrier) (f q : Lp ℝ 2 μ) :
    inner ℝ (scalarValue g μ f) (scalarValue g μ q) = inner ℝ f q := by
  rw [scalarValue, scalarValue, realizeActualForm_inner, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [scalarForm_inner]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]

theorem scalarValue_norm (g : SmoothMetric M) (μ : Measure M.Carrier) (f : Lp ℝ 2 μ) :
    ‖scalarValue g μ f‖ = ‖f‖ := by
  have he := scalarValue_inner g μ f f
  simp only [real_inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

def scalarLinear (g : SmoothMetric M) (μ : Measure M.Carrier) :
    Lp ℝ 2 μ →ₗ[ℝ] L2FormHilbert g μ 0 where
  toFun := scalarValue g μ
  map_add' f q := by
    change realizeActualForm g μ (scalarForm (fun x => (f + q : Lp ℝ 2 μ) x)) _ =
      realizeActualForm g μ (scalarForm f) _ + realizeActualForm g μ (scalarForm q) _
    rw [← realizeActualForm_add g μ (scalarForm f) (scalarForm q)]
    apply (realizeL2Form_eq_iff_ae g μ _ _).mpr
    filter_upwards [Lp.coeFn_add f q] with x hx
    ext V
    change (f + q : Lp ℝ 2 μ) x = f x + q x
    exact hx
  map_smul' c f := by
    change realizeActualForm g μ (scalarForm (fun x => (c • f : Lp ℝ 2 μ) x)) _ =
      c • realizeActualForm g μ (scalarForm f) _
    have hr : realizeActualForm g μ (c • scalarForm f)
        (l2RealForm_smul g μ c _ (scalar_l2 g μ f)) = c • scalarValue g μ f :=
      (UniformSpace.Completion.toComplL : L2FormSpace g μ 0 →L[ℝ] L2FormHilbert g μ 0).map_smul
        c (L2FormSpace.ofSection (scalarForm f) (scalar_l2 g μ f))
    change realizeActualForm g μ (c • scalarForm f) _ = c • realizeActualForm g μ (scalarForm f) _ at hr
    rw [← hr]
    apply (realizeL2Form_eq_iff_ae g μ _ _).mpr
    filter_upwards [Lp.coeFn_smul c f] with x hx
    ext V
    change (c • f : Lp ℝ 2 μ) x = c * f x
    exact hx

def scalarLift (g : SmoothMetric M) (μ : Measure M.Carrier) :
    Lp ℝ 2 μ →L[ℝ] L2FormHilbert g μ 0 :=
  (scalarLinear g μ).mkContinuous 1 (fun f => by
    change ‖scalarValue g μ f‖ ≤ 1 * ‖f‖
    rw [one_mul, scalarValue_norm])

theorem scalarLift_inner (g : SmoothMetric M) (μ : Measure M.Carrier) (f q : Lp ℝ 2 μ) :
    inner ℝ (scalarLift g μ f) (scalarLift g μ q) = inner ℝ f q := scalarValue_inner g μ f q

theorem scalarLift_injective (g : SmoothMetric M) (μ : Measure M.Carrier) :
    Function.Injective (scalarLift g μ) := by
  intro f q he
  have hz : scalarLift g μ (f - q) = 0 := by rw [map_sub, he, sub_self]
  have hn := scalarValue_norm g μ (f - q)
  change ‖scalarLift g μ (f - q)‖ = ‖f - q‖ at hn
  rw [hz, norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)

theorem scalarLift_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : Lp ℝ 2 μ) (q : M.Carrier → ℝ) (hq : L2RealForm g.form μ (scalarForm q))
    (heq : f =ᵐ[μ] q) :
    scalarLift g μ f = realizeActualForm g μ (scalarForm q) hq := by
  apply (realizeL2Form_eq_iff_ae g μ _ _).mpr
  filter_upwards [heq] with x hx
  ext V
  exact hx

theorem scalar_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : M.Carrier → ℝ) (hf : L2RealForm g.form μ (scalarForm f)) : MemLp f 2 μ := by
  have h1 : SmoothRealForm (scalarForm (fun _ : M.Carrier => (1 : ℝ))) :=
    scalarForm_smooth _ (fun _ => contDiffOn_const)
  have hm := formInner_aestronglyMeasurable_of_coefficients g μ (scalarForm f)
    (scalarForm (fun _ => (1 : ℝ))) hf.1 (smoothRealForm_coefficient_aestronglyMeasurable μ _ h1)
  have hfm : AEStronglyMeasurable f μ := hm.congr (Filter.Eventually.of_forall fun x => by
    rw [scalarForm_inner, mul_one])
  apply (memLp_two_iff_integrable_sq hfm).mpr
  exact (formNormSq_integrable g μ _ hf).congr (Filter.Eventually.of_forall fun x =>
    scalarForm_normSq g.form f x)

theorem scalarLift_toLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : M.Carrier → ℝ) (hf : L2RealForm g.form μ (scalarForm f)) :
    scalarLift g μ ((scalar_memLp g μ f hf).toLp f) =
      realizeActualForm g μ (scalarForm f) hf :=
  scalarLift_realize g μ _ f hf (scalar_memLp g μ f hf).coeFn_toLp

end Yau.NodeProofs.P06Aux.TraceHilbert
