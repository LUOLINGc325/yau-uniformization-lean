import Yau.LeafProofs.L19ScalarResolvent
import Yau.LeafProofs.L19SmoothDensity
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! Complexification on the actual scalar L² spaces. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual time-one variational resolvent has trivial kernel. -/
theorem scalarResolvent_one_injective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    Function.Injective (scalarResolvent g μ hμ 1 zero_lt_one) := by
  have hJ : Function.Injective (scalarEnergyL2 g μ hμ).adjoint := by
    intro f k hfk
    apply ext_inner_right ℝ
    intro v
    refine (scalarEnergyL2_denseRange g μ hμ).induction_on v
      (isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner continuous_id)) ?_
    intro w
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.adjoint_inner_left, hfk]
  rw [scalarResolvent_one_eq]
  exact (scalarEnergyL2 g μ hμ).self_comp_adjoint_injective_iff.mpr hJ

/-- Self-adjointness and trivial kernel give dense range in actual L². -/
theorem scalarResolvent_one_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    DenseRange (scalarResolvent g μ hμ 1 zero_lt_one) := by
  have hk : (scalarResolvent g μ hμ 1 zero_lt_one).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (scalarResolvent_one_injective g μ hμ)
  have heq := (scalarResolvent g μ hμ 1 zero_lt_one).orthogonal_ker
  rw [hk, Submodule.bot_orthogonal_eq_top, scalarResolvent_one_adjoint] at heq
  intro f
  have hf : f ∈ (scalarResolvent g μ hμ 1 zero_lt_one).range.topologicalClosure := by
    rw [← heq]
    trivial
  exact hf

section Lp
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Real, imaginary and real-inclusion maps on the original L² spaces. -/
def heatLpRe : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ
def heatLpIm : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.imCLM.compLpL 2 μ
def heatLpOfReal : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

theorem heatLpRe_ae (f : Lp ℂ 2 μ) : heatLpRe μ f =ᵐ[μ] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f
theorem heatLpIm_ae (f : Lp ℂ 2 μ) : heatLpIm μ f =ᵐ[μ] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLpL f
theorem heatLpOfReal_ae (f : Lp ℝ 2 μ) : heatLpOfReal μ f =ᵐ[μ] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

@[simp] theorem heatLpRe_ofReal (f : Lp ℝ 2 μ) : heatLpRe μ (heatLpOfReal μ f) = f := by
  apply Lp.ext
  filter_upwards [heatLpRe_ae μ (heatLpOfReal μ f), heatLpOfReal_ae μ f] with x h₁ h₂
  simp [h₁, h₂]
@[simp] theorem heatLpIm_ofReal (f : Lp ℝ 2 μ) : heatLpIm μ (heatLpOfReal μ f) = 0 := by
  apply Lp.ext
  filter_upwards [heatLpIm_ae μ (heatLpOfReal μ f), heatLpOfReal_ae μ f, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)]
    with x h₁ h₂ h₀
  simpa only [h₁, h₂, Complex.ofReal_im, Pi.zero_apply] using h₀.symm

theorem heatLpRe_smul (c : ℂ) (f : Lp ℂ 2 μ) :
    heatLpRe μ (c • f) = c.re • heatLpRe μ f - c.im • heatLpIm μ f := by
  apply Lp.ext
  filter_upwards [heatLpRe_ae μ (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_sub (c.re • heatLpRe μ f) (c.im • heatLpIm μ f),
    Lp.coeFn_smul c.re (heatLpRe μ f), Lp.coeFn_smul c.im (heatLpIm μ f),
    heatLpRe_ae μ f, heatLpIm_ae μ f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [h₁, h₂, h₃, Pi.sub_apply, Pi.smul_apply, h₄, h₅, h₆, h₇, smul_eq_mul, Complex.mul_re]

theorem heatLpIm_smul (c : ℂ) (f : Lp ℂ 2 μ) :
    heatLpIm μ (c • f) = c.re • heatLpIm μ f + c.im • heatLpRe μ f := by
  apply Lp.ext
  filter_upwards [heatLpIm_ae μ (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_add (c.re • heatLpIm μ f) (c.im • heatLpRe μ f),
    Lp.coeFn_smul c.re (heatLpIm μ f), Lp.coeFn_smul c.im (heatLpRe μ f),
    heatLpRe_ae μ f, heatLpIm_ae μ f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [h₁, h₂, h₃, Pi.add_apply, Pi.smul_apply, h₄, h₅, h₆, h₇, smul_eq_mul, Complex.mul_im]

/-- Every original complex L² function decomposes into its actual real and
imaginary parts. -/
theorem heatLp_decomposition (f : Lp ℂ 2 μ) :
    heatLpOfReal μ (heatLpRe μ f) + Complex.I • heatLpOfReal μ (heatLpIm μ f) = f := by
  apply Lp.ext
  filter_upwards [heatLpRe_ae μ f, heatLpIm_ae μ f,
    heatLpOfReal_ae μ (heatLpRe μ f), heatLpOfReal_ae μ (heatLpIm μ f),
    Lp.coeFn_add (heatLpOfReal μ (heatLpRe μ f)) (Complex.I • heatLpOfReal μ (heatLpIm μ f)),
    Lp.coeFn_smul Complex.I (heatLpOfReal μ (heatLpIm μ f))] with x h₁ h₂ h₃ h₄ h₅ h₆
  simp only [h₅, Pi.add_apply, h₆, Pi.smul_apply, h₃, h₄, h₁, h₂, smul_eq_mul]
  simpa [mul_comm] using Complex.re_add_im (f x)

/-- The real inclusion preserves the L² inner product. -/
theorem heatLpOfReal_inner (f k : Lp ℝ 2 μ) :
    ⟪heatLpOfReal μ f, heatLpOfReal μ k⟫_ℂ = (⟪f, k⟫_ℝ : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [heatLpOfReal_ae μ f, heatLpOfReal_ae μ k] with x hf hk
  simp [hf, hk, RCLike.inner_apply]

/-- The real and imaginary parts split the squared L² norm. -/
theorem heatLp_norm_sq (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ‖heatLpRe μ f‖ ^ 2 + ‖heatLpIm μ f‖ ^ 2 := by
  have h := congrArg Complex.re (show
    ⟪heatLpOfReal μ (heatLpRe μ f) + Complex.I • heatLpOfReal μ (heatLpIm μ f),
      heatLpOfReal μ (heatLpRe μ f) + Complex.I • heatLpOfReal μ (heatLpIm μ f)⟫_ℂ =
      ⟪f, f⟫_ℂ from congrArg (fun v : Lp ℂ 2 μ => ⟪v, v⟫_ℂ) (heatLp_decomposition μ f))
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    heatLpOfReal_inner, Complex.conj_I] at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    inner_self_eq_norm_sq_to_K f] at h
  simp only [← Complex.ofReal_pow, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, mul_one, one_mul,
    zero_sub, sub_zero, add_zero, neg_zero, neg_neg] at h
  change _ = ((‖f‖ : ℂ) ^ 2).re at h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at h
  linarith

/-- Complexification of a real operator on the actual L² function spaces. -/
def heatComplexifyReal (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (heatLpOfReal μ).comp (T.comp (heatLpRe μ)) +
    Complex.I • (heatLpOfReal μ).comp (T.comp (heatLpIm μ))

@[simp] theorem heatComplexifyReal_apply (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    heatComplexifyReal μ T f = heatLpOfReal μ (T (heatLpRe μ f)) +
      Complex.I • heatLpOfReal μ (T (heatLpIm μ f)) := rfl

theorem heatLp_smul_split (c : ℂ) (f : Lp ℂ 2 μ) :
    c • f = c.re • f + Complex.I • (c.im • f) := by
  have hc : c = (c.re : ℂ) + Complex.I * (c.im : ℂ) := by
    simpa [mul_comm] using (Complex.re_add_im c).symm
  conv_lhs => rw [hc, add_smul, mul_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c.re f,
    RCLike.real_smul_eq_coe_smul (K := ℂ) c.im f]
  rfl

def heatComplexify (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ where
  toFun := heatComplexifyReal μ T
  map_add' := (heatComplexifyReal μ T).map_add
  map_smul' c f := by
    simp only [heatComplexifyReal_apply, heatLpRe_smul, heatLpIm_smul, map_sub,
      map_add, map_smul, RingHom.id_apply]
    conv_rhs => rw [heatLp_smul_split μ c]
    simp only [smul_add, smul_sub, smul_comm Complex.I (c.re : ℝ),
      smul_comm Complex.I (c.im : ℝ)]
    rw [smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_smul, one_smul]
    simp only [smul_neg]
    abel
  cont := (heatComplexifyReal μ T).continuous

@[simp] theorem heatComplexify_apply (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    heatComplexify μ T f = heatLpOfReal μ (T (heatLpRe μ f)) +
      Complex.I • heatLpOfReal μ (T (heatLpIm μ f)) := rfl

@[simp] theorem heatComplexify_re (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    heatLpRe μ (heatComplexify μ T f) = T (heatLpRe μ f) := by
  simp [heatComplexify_apply, map_add, heatLpRe_smul]

@[simp] theorem heatComplexify_im (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    heatLpIm μ (heatComplexify μ T f) = T (heatLpIm μ f) := by
  simp [heatComplexify_apply, map_add, heatLpIm_smul]

@[simp] theorem heatComplexify_ofReal (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 μ) :
    heatComplexify μ T (heatLpOfReal μ f) = heatLpOfReal μ (T f) := by
  simp

theorem heatLp_re_inner (f k : Lp ℂ 2 μ) :
    (⟪f, k⟫_ℂ).re = ⟪heatLpRe μ f, heatLpRe μ k⟫_ℝ +
      ⟪heatLpIm μ f, heatLpIm μ k⟫_ℝ := by
  calc
    _ = (⟪heatLpOfReal μ (heatLpRe μ f) + Complex.I • heatLpOfReal μ (heatLpIm μ f),
      heatLpOfReal μ (heatLpRe μ k) + Complex.I • heatLpOfReal μ (heatLpIm μ k)⟫_ℂ).re := by
        rw [heatLp_decomposition, heatLp_decomposition]
    _ = _ := by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        heatLpOfReal_inner, Complex.conj_I, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring

theorem heatComplexify_norm_le (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f, ‖T f‖ ≤ ‖f‖) (f : Lp ℂ 2 μ) : ‖heatComplexify μ T f‖ ≤ ‖f‖ := by
  have h₁ := hT (heatLpRe μ f)
  have h₂ := hT (heatLpIm μ f)
  have hsq := heatLp_norm_sq μ (heatComplexify μ T f)
  rw [heatComplexify_re, heatComplexify_im] at hsq
  have hf := heatLp_norm_sq μ f
  nlinarith [norm_nonneg (T (heatLpRe μ f)), norm_nonneg (T (heatLpIm μ f)),
    norm_nonneg (heatLpRe μ f), norm_nonneg (heatLpIm μ f),
    norm_nonneg (heatComplexify μ T f), norm_nonneg f]

theorem heatComplexify_isSymmetric (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : T.IsSymmetric) : (heatComplexify μ T).IsSymmetric := by
  intro f k
  change ⟪heatComplexify μ T f, k⟫_ℂ = ⟪f, heatComplexify μ T k⟫_ℂ
  conv_lhs => rw [← heatLp_decomposition μ k]
  conv_rhs => rw [← heatLp_decomposition μ f]
  simp only [heatComplexify_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, heatLpOfReal_inner]
  have hs (a b : Lp ℝ 2 μ) : ⟪T a, b⟫_ℝ = ⟪a, T b⟫_ℝ := hT a b
  simp only [hs]

theorem heatComplexify_re_inner_nonneg (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f, 0 ≤ ⟪T f, f⟫_ℝ) (f : Lp ℂ 2 μ) :
    0 ≤ (⟪heatComplexify μ T f, f⟫_ℂ).re := by
  rw [heatLp_re_inner, heatComplexify_re, heatComplexify_im]
  exact add_nonneg (hT _) (hT _)

theorem heatComplexify_injective (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : Function.Injective T) : Function.Injective (heatComplexify μ T) := by
  intro f k hfk
  have hr := congrArg (heatLpRe μ) hfk
  have hi := congrArg (heatLpIm μ) hfk
  simp only [heatComplexify_re] at hr
  simp only [heatComplexify_im] at hi
  rw [← heatLp_decomposition μ f, ← heatLp_decomposition μ k, hT hr, hT hi]

end Lp
/-- The complexified operator is fixed by the genuine variational resolvent. -/
def scalarComplexResolvent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  heatComplexify μ (scalarResolvent g μ hμ 1 zero_lt_one)

theorem scalarComplexResolvent_positive (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : (scalarComplexResolvent g μ hμ).IsPositive := by
  refine ⟨heatComplexify_isSymmetric μ _ ?_, ?_⟩
  · exact (ContinuousLinearMap.eq_adjoint_iff _ _).mp
      (scalarResolvent_one_adjoint g μ hμ).symm
  · exact heatComplexify_re_inner_nonneg μ _ (scalarResolvent_one_inner_nonneg g μ hμ)

theorem scalarComplexResolvent_selfAdjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : IsSelfAdjoint (scalarComplexResolvent g μ hμ) :=
  (scalarComplexResolvent_positive g μ hμ).isSelfAdjoint

theorem scalarComplexResolvent_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℂ 2 μ) :
    ‖scalarComplexResolvent g μ hμ f‖ ≤ ‖f‖ :=
  heatComplexify_norm_le μ _ (scalarResolvent_norm_le g μ hμ 1 zero_lt_one) f

theorem scalarComplexResolvent_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : ‖scalarComplexResolvent g μ hμ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using scalarComplexResolvent_norm_le g μ hμ f

theorem scalarComplexResolvent_injective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Function.Injective (scalarComplexResolvent g μ hμ) :=
  heatComplexify_injective μ _ (scalarResolvent_one_injective g μ hμ)

theorem scalarComplexResolvent_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : DenseRange (scalarComplexResolvent g μ hμ) := by
  have hk : (scalarComplexResolvent g μ hμ).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (scalarComplexResolvent_injective g μ hμ)
  have heq := (scalarComplexResolvent g μ hμ).orthogonal_ker
  have hs : (scalarComplexResolvent g μ hμ).adjoint = scalarComplexResolvent g μ hμ :=
    (scalarComplexResolvent_selfAdjoint g μ hμ).star_eq
  rw [hk, Submodule.bot_orthogonal_eq_top, hs] at heq
  intro f
  have hf : f ∈ (scalarComplexResolvent g μ hμ).range.topologicalClosure := by
    rw [← heq]
    trivial
  exact hf

/-- The real spectrum of the constructed complex resolvent lies in `[0,1]`. -/
theorem scalarComplexResolvent_spectrum (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    spectrum ℝ (scalarComplexResolvent g μ hμ) ⊆ Set.Icc 0 1 := by
  intro s hs
  have hpos : 0 ≤ scalarComplexResolvent g μ hμ :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (scalarComplexResolvent_positive g μ hμ)
  refine ⟨spectrum_nonneg_of_nonneg hpos hs, ?_⟩
  have hn := spectrum.norm_le_norm_mul_of_mem hs
  have hI : ‖(1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hop := scalarComplexResolvent_opNorm_le g μ hμ
  have hmul := mul_le_mul hop hI (norm_nonneg _) zero_le_one
  exact (le_abs_self s).trans (hn.trans (by simpa using hmul))

@[simp] theorem scalarComplexResolvent_ofReal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    scalarComplexResolvent g μ hμ (heatLpOfReal μ f) =
      heatLpOfReal μ (scalarResolvent g μ hμ 1 zero_lt_one f) := by
  exact heatComplexify_ofReal μ _ f

end Yau.LeafProofs.L19Aux
