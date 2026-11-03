import Yau.Proofs.P06ComplexHilbert
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

noncomputable section
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux.ComplexHilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def reCLM : ComplexHilbert H →L[ℝ] H where
  toFun := re
  map_add' := re_add
  map_smul' := re_real_smul
  cont := (WithLp.fstL 2 ℝ H H).continuous

def imCLM : ComplexHilbert H →L[ℝ] H where
  toFun := im
  map_add' := im_add
  map_smul' := im_real_smul
  cont := (WithLp.sndL 2 ℝ H H).continuous

def ofRealCLM : H →L[ℝ] ComplexHilbert H where
  toFun x := mk x 0
  map_add' x y := by apply ext <;> simp
  map_smul' r x := by apply ext <;> simp
  cont := (WithLp.prod_continuous_toLp 2 H H).comp (continuous_id.prodMk continuous_const)

@[simp] theorem reCLM_apply (x : ComplexHilbert H) : reCLM x = re x := rfl
@[simp] theorem imCLM_apply (x : ComplexHilbert H) : imCLM x = im x := rfl
@[simp] theorem ofRealCLM_apply (x : H) : ofRealCLM x = mk x 0 := rfl
@[simp] theorem re_ofReal (x : H) : re (ofRealCLM x) = x := rfl
@[simp] theorem im_ofReal (x : H) : im (ofRealCLM x) = 0 := rfl

theorem decomposition (x : ComplexHilbert H) :
    ofRealCLM (re x) + Complex.I • ofRealCLM (im x) = x := by
  apply ext <;> simp

theorem ofReal_norm (x : H) : ‖(ofRealCLM x : ComplexHilbert H)‖ = ‖x‖ := by
  have hs := norm_sq (ofRealCLM x : ComplexHilbert H)
  simp only [re_ofReal, im_ofReal, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hs
  nlinarith [norm_nonneg (ofRealCLM x : ComplexHilbert H), norm_nonneg x]

theorem ofReal_inner (x y : H) :
    inner ℂ (ofRealCLM x : ComplexHilbert H) (ofRealCLM y) = (inner ℝ x y : ℂ) := by
  simp [inner_apply, innerC]

def complexifyReal (T : H →L[ℝ] H) : ComplexHilbert H →L[ℝ] ComplexHilbert H where
  toFun x := mk (T (re x)) (T (im x))
  map_add' x y := by apply ext <;> simp
  map_smul' r x := by apply ext <;> simp
  cont := (WithLp.prod_continuous_toLp 2 H H).comp
    ((T.continuous.comp reCLM.continuous).prodMk (T.continuous.comp imCLM.continuous))

@[simp] theorem complexifyReal_re (T : H →L[ℝ] H) (x : ComplexHilbert H) :
    re (complexifyReal T x) = T (re x) := rfl
@[simp] theorem complexifyReal_im (T : H →L[ℝ] H) (x : ComplexHilbert H) :
    im (complexifyReal T x) = T (im x) := rfl

def complexify (T : H →L[ℝ] H) : ComplexHilbert H →L[ℂ] ComplexHilbert H where
  toFun := complexifyReal T
  map_add' := (complexifyReal T).map_add
  map_smul' c x := by
    apply ext <;> simp only [complexifyReal_re, complexifyReal_im, re_smul, im_smul,
      map_sub, map_add, map_smul, RingHom.id_apply]
  cont := (complexifyReal T).continuous

@[simp] theorem complexify_re (T : H →L[ℝ] H) (x : ComplexHilbert H) :
    re (complexify T x) = T (re x) := rfl
@[simp] theorem complexify_im (T : H →L[ℝ] H) (x : ComplexHilbert H) :
    im (complexify T x) = T (im x) := rfl

@[simp] theorem complexify_ofReal (T : H →L[ℝ] H) (x : H) :
    complexify T (ofRealCLM x) = ofRealCLM (T x) := by
  apply ext <;> simp

theorem complexify_norm_le (T : H →L[ℝ] H) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (x : ComplexHilbert H) : ‖complexify T x‖ ≤ ‖x‖ := by
  have h₁ := hT (re x)
  have h₂ := hT (im x)
  have hs := norm_sq (complexify T x)
  rw [complexify_re, complexify_im] at hs
  have hx := norm_sq x
  nlinarith [norm_nonneg (T (re x)), norm_nonneg (T (im x)),
    norm_nonneg (re x), norm_nonneg (im x), norm_nonneg (complexify T x), norm_nonneg x]

theorem complexify_symmetric (T : H →L[ℝ] H) (hT : T.IsSymmetric) : (complexify T).IsSymmetric := by
  intro x y
  change inner ℂ (complexify T x) y = inner ℂ x (complexify T y)
  have hsym (a b : H) : inner ℝ (T a) b = inner ℝ a (T b) := hT a b
  apply Complex.ext <;> simp only [inner_apply, innerC_re, innerC_im,
    complexify_re, complexify_im, hsym]

theorem complexify_inner_nonnegative (T : H →L[ℝ] H)
    (hT : ∀ x, 0 ≤ inner ℝ (T x) x) (x : ComplexHilbert H) :
    0 ≤ (inner ℂ (complexify T x) x).re := by
  rw [inner_apply, innerC_re, complexify_re, complexify_im]
  exact add_nonneg (hT _) (hT _)

variable [CompleteSpace H]

theorem complexify_positive (T : H →L[ℝ] H) (hs : T.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (T x) x) : (complexify T).IsPositive :=
  ⟨complexify_symmetric T hs, complexify_inner_nonnegative T hp⟩

theorem complexify_injective (T : H →L[ℝ] H) (hT : Function.Injective T) :
    Function.Injective (complexify T) := by
  intro x y hxy
  apply ext
  · apply hT
    simpa only [complexify_re] using congrArg re hxy
  · apply hT
    simpa only [complexify_im] using congrArg im hxy

theorem complexify_selfAdjoint (T : H →L[ℝ] H) (hT : T.IsSymmetric) : IsSelfAdjoint (complexify T) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (complexify_symmetric T hT)

theorem complexify_denseRange (T : H →L[ℝ] H) (hs : T.IsSymmetric) (hi : Function.Injective T) :
    DenseRange (complexify T) := by
  have hk : (complexify T).ker = ⊥ := LinearMap.ker_eq_bot.mpr (complexify_injective T hi)
  have heq := (complexify T).orthogonal_ker
  have hAdj : (complexify T).adjoint = complexify T := (complexify_selfAdjoint T hs).star_eq
  rw [hk, Submodule.bot_orthogonal_eq_top, hAdj] at heq
  intro x
  have hx : x ∈ (complexify T).range.topologicalClosure := by rw [← heq]; trivial
  exact hx

/-- Every real-valued continuous functional calculus of the actual diagonal
complexification preserves the genuine real subspace. -/
theorem complexify_cfc_im_zero (T : H →L[ℝ] H) (hs : T.IsSymmetric) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (spectrum ℝ (complexify T))) (x : ComplexHilbert H) (hx : im x = 0) :
    im (cfc φ (complexify T) x) = 0 := by
  let B := complexify T
  have hB : IsSelfAdjoint B := complexify_selfAdjoint T hs
  have hBim (x : ComplexHilbert H) (hx : im x = 0) : im (B x) = 0 := by
    change T (im x) = 0
    rw [hx, map_zero]
  have hall (F : C(spectrum ℝ B, ℝ)) : ∀ x : ComplexHilbert H,
      im x = 0 → im (cfcHom hB F x) = 0 := by
    induction F using ContinuousMap.induction_on_of_compact with
    | const r =>
        intro x hx
        have hc : cfcHom hB (ContinuousMap.const (spectrum ℝ B) r) =
            algebraMap ℝ (ComplexHilbert H →L[ℂ] ComplexHilbert H) r := (cfcHom hB).commutes r
        rw [hc, Algebra.algebraMap_eq_smul_one, smul_apply,
          one_apply_eq_self, im_real_smul, hx, smul_zero]
    | id =>
        intro x hx
        rw [cfcHom_id]
        exact hBim x hx
    | star_id =>
        intro x hx
        rw [map_star, cfcHom_id, hB.star_eq]
        exact hBim x hx
    | add F G hF hG =>
        intro x hx
        rw [map_add, add_apply, im_add, hF x hx, hG x hx, add_zero]
    | mul F G hF hG =>
        intro x hx
        rw [map_mul, mul_apply_eq_comp]
        exact hF _ (hG x hx)
    | frequently F hF =>
        intro x hx
        have hcont : Continuous (fun G : C(spectrum ℝ B, ℝ) => im (cfcHom hB G x)) :=
          imCLM.continuous.comp
            ((ContinuousLinearMap.apply ℂ (ComplexHilbert H) x).continuous.comp (cfcHom_continuous hB))
        exact isClosed_singleton.mem_of_frequently_of_tendsto
          (hF.mono fun G hG => hG x hx) (hcont.tendsto F)
  rw [cfc_apply φ (complexify T) hB hφ]
  exact hall _ x hx

end Yau.NodeProofs.P06Aux.ComplexHilbert
