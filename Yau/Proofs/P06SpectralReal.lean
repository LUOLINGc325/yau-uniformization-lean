import Yau.Proofs.P06SpectralHeat

noncomputable section
open Filter ContinuousLinearMap
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux.Spectral
open Yau.LeafProofs.L19Aux
open ComplexHilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
  (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R)

theorem complexHeat_im_zero (t : ℝ) (x : ComplexHilbert H) (hx : im x = 0) :
    im (complexHeat R hRs hRp hRb hRi t x) = 0 := by
  unfold complexHeat
  split_ifs with ht
  · exact ComplexHilbert.complexify_cfc_im_zero R hRs _
      (scalarHeatMultiplier_continuous ht).continuousOn x hx
  · simpa only [one_apply_eq_self] using hx

def realHeat (t : ℝ) : H →L[ℝ] H :=
  reCLM.comp (((complexHeat R hRs hRp hRb hRi t).restrictScalars ℝ).comp ofRealCLM)

theorem ofReal_injective : Function.Injective (ofRealCLM : H →L[ℝ] ComplexHilbert H) := by
  intro x y hxy
  simpa only [re_ofReal] using congrArg re hxy

theorem realHeat_ofReal (t : ℝ) (x : H) :
    ofRealCLM (realHeat R hRs hRp hRb hRi t x) = complexHeat R hRs hRp hRb hRi t (ofRealCLM x) := by
  have hd := decomposition (complexHeat R hRs hRp hRb hRi t (ofRealCLM x))
  rw [complexHeat_im_zero R hRs hRp hRb hRi t _ (im_ofReal x), map_zero, smul_zero, add_zero] at hd
  exact hd

@[simp] theorem realHeat_zero : realHeat R hRs hRp hRb hRi 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change re (complexHeat R hRs hRp hRb hRi 0 (ofRealCLM x)) = x
  rw [complexHeat_zero, one_apply_eq_self, re_ofReal]

theorem realHeat_norm_le (t : ℝ) (x : H) : ‖realHeat R hRs hRp hRb hRi t x‖ ≤ ‖x‖ := by
  rw [← ComplexHilbert.ofReal_norm (realHeat R hRs hRp hRb hRi t x), realHeat_ofReal]
  exact (complexHeat_norm_le R hRs hRp hRb hRi t _).trans_eq (ComplexHilbert.ofReal_norm x)

theorem realHeat_symmetric (t : ℝ) : (realHeat R hRs hRp hRb hRi t).IsSymmetric := by
  intro x y
  change inner ℝ (realHeat R hRs hRp hRb hRi t x) y =
    inner ℝ x (realHeat R hRs hRp hRb hRi t y)
  apply Complex.ofReal_injective
  rw [← ofReal_inner, ← ofReal_inner, realHeat_ofReal, realHeat_ofReal]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (complexHeat_selfAdjoint R hRs hRp hRb hRi t)) (ofRealCLM x) (ofRealCLM y)

theorem realHeat_adjoint (t : ℝ) : (realHeat R hRs hRp hRb hRi t).adjoint =
    realHeat R hRs hRp hRb hRi t :=
  LinearMap.IsSymmetric.clm_adjoint_eq (realHeat_symmetric R hRs hRp hRb hRi t)

theorem realHeat_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    realHeat R hRs hRp hRb hRi (s + t) =
      realHeat R hRs hRp hRb hRi s * realHeat R hRs hRp hRb hRi t := by
  apply ContinuousLinearMap.ext
  intro x
  apply ofReal_injective
  rw [mul_apply_eq_comp, realHeat_ofReal, realHeat_ofReal, realHeat_ofReal,
    complexHeat_add R hRs hRp hRb hRi hs ht, mul_apply_eq_comp]

theorem realHeat_tendsto_zero (x : H) :
    Tendsto (fun t : ℝ => realHeat R hRs hRp hRb hRi t x) (𝓝[≥] (0 : ℝ)) (𝓝 x) := by
  have h := reCLM.continuous.tendsto (ofRealCLM x : ComplexHilbert H) |>.comp
    (complexHeat_tendsto_zero R hRs hRp hRb hRi (ofRealCLM x))
  simpa only [Function.comp_def, realHeat, comp_apply, coe_restrictScalars',
    reCLM_apply, re_ofReal] using h

theorem complexHeatInverse_im_zero {t : ℝ} (ht : 0 < t) (x : ComplexHilbert H) (hx : im x = 0) :
    im (complexHeatInverse R hRs hRp hRb hRi t x) = 0 :=
  ComplexHilbert.complexify_cfc_im_zero R hRs _
    (scalarHeatInverseMultiplier_continuous ht).continuousOn x hx

def realHeatInverse (t : ℝ) : H →L[ℝ] H :=
  reCLM.comp (((complexHeatInverse R hRs hRp hRb hRi t).restrictScalars ℝ).comp ofRealCLM)

theorem realHeatInverse_ofReal {t : ℝ} (ht : 0 < t) (x : H) :
    ofRealCLM (realHeatInverse R hRs hRp hRb hRi t x) =
      complexHeatInverse R hRs hRp hRb hRi t (ofRealCLM x) := by
  have hd := decomposition (complexHeatInverse R hRs hRp hRb hRi t (ofRealCLM x))
  rw [complexHeatInverse_im_zero R hRs hRp hRb hRi ht _ (im_ofReal x),
    map_zero, smul_zero, add_zero] at hd
  exact hd

theorem realHeat_factor {t : ℝ} (ht : 0 < t) :
    realHeat R hRs hRp hRb hRi t = R * realHeatInverse R hRs hRp hRb hRi t := by
  apply ContinuousLinearMap.ext
  intro x
  have hc := congrArg (fun T : ComplexHilbert H →L[ℂ] ComplexHilbert H => re (T (ofRealCLM x)))
    (complexHeat_factor R hRs hRp hRb hRi ht)
  simpa only [mul_apply_eq_comp, complexResolvent, complexify_re, realHeat, realHeatInverse,
    comp_apply, coe_restrictScalars', reCLM_apply] using hc

def realRestrictionCLM : (ComplexHilbert H →L[ℂ] ComplexHilbert H) →L[ℝ] (H →L[ℝ] H) :=
  (ContinuousLinearMap.compL ℝ H (ComplexHilbert H) H reCLM).comp
    (((ContinuousLinearMap.compL ℝ H (ComplexHilbert H) (ComplexHilbert H)).flip ofRealCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (ComplexHilbert H) (ComplexHilbert H) ℝ ℝ))

theorem realRestriction_heat (t : ℝ) :
    realRestrictionCLM (complexHeat R hRs hRp hRb hRi t) = realHeat R hRs hRp hRb hRi t := rfl

theorem realRestriction_inverse (t : ℝ) :
    realRestrictionCLM (complexHeatInverse R hRs hRp hRb hRi t) = realHeatInverse R hRs hRp hRb hRi t := rfl

theorem realHeat_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (realHeat R hRs hRp hRb hRi)
      (realHeat R hRs hRp hRb hRi t - realHeatInverse R hRs hRp hRb hRi t) t := by
  have h := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
    (F := ComplexHilbert H →L[ℂ] ComplexHilbert H) (E := H →L[ℝ] H)
    (f := complexHeat R hRs hRp hRb hRi) t realRestrictionCLM.hasFDerivAt
    (complexHeat_hasDerivAt R hRs hRp hRb hRi ht)
  simpa only [Function.comp_def, map_sub, realRestriction_heat, realRestriction_inverse] using h

theorem realHeat_apply_hasDerivAt {t : ℝ} (ht : 0 < t) (x : H) :
    HasDerivAt (fun s => realHeat R hRs hRp hRb hRi s x)
      (realHeat R hRs hRp hRb hRi t x - realHeatInverse R hRs hRp hRb hRi t x) t := by
  have h := (ContinuousLinearMap.apply ℝ H x).hasFDerivAt.comp_hasDerivAt t
    (realHeat_hasDerivAt R hRs hRp hRb hRi ht)
  change HasDerivAt (fun s => realHeat R hRs hRp hRb hRi s x)
    ((realHeat R hRs hRp hRb hRi t - realHeatInverse R hRs hRp hRb hRi t) x) t at h
  simpa only [sub_apply] using h

end Yau.NodeProofs.P06Aux.Spectral
