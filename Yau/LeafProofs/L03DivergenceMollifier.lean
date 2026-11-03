import Yau.LeafProofs.L03
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory Filter
open scoped Topology ContDiff Convolution

noncomputable section

namespace Yau.LeafProofs.L03

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant]

theorem compact_kernel_mul_integrable (ψ : E → ℝ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (u : E → ℝ) (hu : Integrable u ν) (x : E) :
    Integrable (fun y => ψ (x - y) * u y) ν := by
  obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ
  exact (hu.bdd_smul C (hψ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hC (x - y))).congr
    (Filter.Eventually.of_forall fun _ => rfl)

theorem convolution_directional_derivative_fun (ρ u : E → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ)
    (hu : Integrable u ν) (v : E) :
    (fun x => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) x v) =
      (fun z => fderiv ℝ ρ z v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u := by
  funext x
  rw [convolution_directional_derivative ν ρ u hρ hcρ hu,
    MeasureTheory.convolution_lsmul_swap]
  rfl

theorem convolution_second_directional_derivative (ρ u : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hu : Integrable u ν) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) y v) x w =
      ∫ y, fderiv ℝ (fun z => fderiv ℝ ρ z v) (x - y) w * u y ∂ν := by
  rw [convolution_directional_derivative_fun ν ρ u (hρ.of_le (by simp)) hcρ hu]
  exact convolution_directional_derivative ν _ u
    ((hρ.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const)
    (hcρ.fderiv_apply ℝ v) hu x w

theorem directional_second_derivative_eq (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  have h := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  exact DFunLike.congr_fun h w

theorem directional_second_derivative_symmetric (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [directional_second_derivative_eq f hf, directional_second_derivative_eq f hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) w v

theorem translated_kernel_derivative (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (x y v : E) :
    fderiv ℝ (fun z => ρ (x - z)) y v = -fderiv ℝ ρ (x - y) v := by
  have hd := (((hρ.differentiable (by simp) (x - y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.id_apply, map_neg] using DFunLike.congr_fun hd v

theorem translated_kernel_second_derivative (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (x y v w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => ρ (x - t)) z v) y w =
      fderiv ℝ (fun z => fderiv ℝ ρ z w) (x - y) v := by
  have heq : (fun z => fderiv ℝ (fun t => ρ (x - t)) z v) =
      (fun z => -(fderiv ℝ ρ (x - z) v)) :=
    funext fun z => translated_kernel_derivative ρ hρ x z v
  rw [heq]
  have hdir : ContDiff ℝ ∞ (fun z => fderiv ℝ ρ z v) :=
    (hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hd := ((((hdir.differentiable (by simp) (x - y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)).neg).fderiv
  have he : fderiv ℝ (fun z => -(fderiv ℝ ρ (x - z) v)) y w =
      fderiv ℝ (fun z => fderiv ℝ ρ z v) (x - y) w := by
    have hdv := DFunLike.congr_fun hd w
    change fderiv ℝ (fun z => -(fderiv ℝ ρ (x - z) v)) y w = _ at hdv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply, map_neg, neg_neg] using hdv
  exact he.trans (directional_second_derivative_symmetric ρ hρ (x - y) v w)

/-- Convolving the formal-transpose principal term gives a genuine
smooth divergence flux, with no derivative of the rough input. -/
theorem translated_kernel_principal_identity (a ρ u : E → ℝ)
    (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (v w : E) (hau : Integrable (fun y => a y * u y) ν)
    (hdau : Integrable (fun y => fderiv ℝ a y w * u y) ν) (x : E) :
    -(∫ y, (a y * fderiv ℝ (fun z => fderiv ℝ (fun t => ρ (x - t)) z v) y w +
        fderiv ℝ a y w * fderiv ℝ (fun t => ρ (x - t)) y v) * u y ∂ν) =
      -fderiv ℝ (fun z => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => a y * u y)) z w) x v +
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => fderiv ℝ a y w * u y)) x v := by
  have hdρ : ContDiff ℝ ∞ (fun z => fderiv ℝ ρ z w) :=
    (hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hρ2 : Continuous (fun z => fderiv ℝ (fun t => fderiv ℝ ρ t w) z v) :=
    (hdρ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hY := compact_kernel_mul_integrable ν _ hρ2
    ((hcρ.fderiv_apply ℝ w).fderiv_apply ℝ v) _ hau x
  have hZ := compact_kernel_mul_integrable ν _
    (((hρ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous :
      Continuous (fun z => fderiv ℝ ρ z v)) (hcρ.fderiv_apply ℝ v) _ hdau x
  have heq : (fun y => (a y * fderiv ℝ (fun z => fderiv ℝ (fun t => ρ (x - t)) z v) y w +
        fderiv ℝ a y w * fderiv ℝ (fun t => ρ (x - t)) y v) * u y) =
      (fun y => fderiv ℝ (fun z => fderiv ℝ ρ z w) (x - y) v * (a y * u y) -
        fderiv ℝ ρ (x - y) v * (fderiv ℝ a y w * u y)) := by
    funext y
    rw [translated_kernel_derivative ρ hρ, translated_kernel_second_derivative ρ hρ]
    ring
  rw [heq, integral_sub hY hZ,
    convolution_second_directional_derivative ν ρ _ hρ hcρ hau,
    convolution_directional_derivative ν ρ _ (hρ.of_le (by simp)) hcρ hdau]
  ring

/-- The existing first-order Friedrichs kernel is an exact identity of
smooth convolutions even on a raw L¹ input. Every derivative falls on
the kernel or coefficient; no derivative of the raw input is evaluated. -/
theorem friedrichsCommutatorKernel_raw_identity (a ρ u : E → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ)
    (hu : Integrable u ν) (hau : Integrable (fun y => a y * u y) ν)
    (v : E) (hdau : Integrable (fun y => fderiv ℝ a y v * u y) ν) (x : E) :
    (∫ y, friedrichsCommutatorKernel a ρ v x y * u y ∂ν) =
      a x * fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) x v -
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => a y * u y)) x v +
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => fderiv ℝ a y v * u y)) x := by
  have hdρ : Continuous (fun z => fderiv ℝ ρ z v) :=
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hbase := compact_kernel_mul_integrable ν _ hdρ (hcρ.fderiv_apply ℝ v) u hu x
  have hY := compact_kernel_mul_integrable ν _ hdρ (hcρ.fderiv_apply ℝ v) _ hau x
  have hZ := compact_kernel_mul_integrable ν ρ hρ.continuous hcρ _ hdau x
  rw [convolution_directional_derivative ν ρ u hρ hcρ hu,
    convolution_directional_derivative ν ρ _ hρ hcρ hau,
    MeasureTheory.convolution_lsmul_swap]
  simp only [smul_eq_mul]
  calc
    _ = ∫ y, a x * (fderiv ℝ ρ (x - y) v * u y) -
        fderiv ℝ ρ (x - y) v * (a y * u y) + ρ (x - y) * (fderiv ℝ a y v * u y) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        unfold friedrichsCommutatorKernel
        ring)
    _ = _ := by
      have hsum := integral_add ((hbase.const_mul (a x)).sub hY) hZ
      have hsub := integral_sub (hbase.const_mul (a x)) hY
      simp only [Pi.sub_apply] at hsum hsub
      rw [hsum, hsub, integral_const_mul]

/-- The rough-input kernel field is actually smooth in its output
variable. This is a consequence of the exact convolution identity. -/
theorem friedrichsCommutatorKernel_raw_contDiff (a ρ u : E → ℝ)
    (ha : ContDiff ℝ ∞ a) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hu : Integrable u ν) (hau : Integrable (fun y => a y * u y) ν)
    (v : E) (hdau : Integrable (fun y => fderiv ℝ a y v * u y) ν) :
    ContDiff ℝ ∞ (fun x => ∫ y, friedrichsCommutatorKernel a ρ v x y * u y ∂ν) := by
  have hconv (f : E → ℝ) (hf : Integrable f ν) :
      ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) :=
    hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hf.locallyIntegrable
  have hdir (f : E → ℝ) (hf : Integrable f ν) :
      ContDiff ℝ ∞ (fun x => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x v) :=
    ((hconv f hf).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have heq : (fun x => ∫ y, friedrichsCommutatorKernel a ρ v x y * u y ∂ν) =
      (fun x => a x * fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) x v -
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => a y * u y)) x v +
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => fderiv ℝ a y v * u y)) x) :=
    funext (friedrichsCommutatorKernel_raw_identity ν a ρ u (hρ.of_le (by simp)) hcρ hu hau v hdau)
  rw [heq]
  exact ((ha.mul (hdir u hu)).sub (hdir _ hau)).add (hconv _ hdau)

/-- The genuine principal flux of the mollified input decomposes into
the convolved raw flux and the already controlled first-order kernel. -/
theorem friedrichsCommutatorKernel_flux_derivative (a ρ u : E → ℝ)
    (ha : ContDiff ℝ ∞ a) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hu : Integrable u ν) (hau : Integrable (fun y => a y * u y) ν)
    (v : E) (hdau : Integrable (fun y => fderiv ℝ a y v * u y) ν) (x w : E) :
    fderiv ℝ (fun z => a z * fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) z v) x w =
      fderiv ℝ (fun z => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => a y * u y)) z v) x w -
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => fderiv ℝ a y v * u y)) x w +
        fderiv ℝ (fun z => ∫ y, friedrichsCommutatorKernel a ρ v z y * u y ∂ν) x w := by
  have hconv (f : E → ℝ) (hf : Integrable f ν) :
      ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) :=
    hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hf.locallyIntegrable
  have hdir : ContDiff ℝ ∞ (fun z => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
      (fun y => a y * u y)) z v) :=
    ((hconv _ hau).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hR := friedrichsCommutatorKernel_raw_contDiff ν a ρ u ha hρ hcρ hu hau v hdau
  have heq : (fun z => a z * fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) z v) =
      (fun z => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => a y * u y)) z v -
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => fderiv ℝ a y v * u y)) z +
        ∫ y, friedrichsCommutatorKernel a ρ v z y * u y ∂ν) := by
    funext z
    rw [friedrichsCommutatorKernel_raw_identity ν a ρ u (hρ.of_le (by simp)) hcρ hu hau v hdau z]
    ring
  rw [heq, fderiv_fun_add
    ((hdir.sub (hconv _ hdau)).differentiable (by simp) x) (hR.differentiable (by simp) x),
    fderiv_fun_sub (hdir.differentiable (by simp) x) ((hconv _ hdau).differentiable (by simp) x)]
  rfl

def multiplicationMollifierCommutator (b ρ u : E → ℝ) (x : E) : ℝ :=
  b x * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) x -
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => b y * u y)) x

theorem multiplicationMollifierCommutator_contDiff (b ρ u : E → ℝ)
    (hb : ContDiff ℝ ∞ b) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hu : Integrable u ν) (hbu : Integrable (fun y => b y * u y) ν) :
    ContDiff ℝ ∞ (multiplicationMollifierCommutator ν b ρ u) :=
  (hb.mul (hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hu.locallyIntegrable)).sub
    (hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hbu.locallyIntegrable)

theorem multiplicationMollifierCommutator_derivative (b ρ u : E → ℝ)
    (hb : ContDiff ℝ ∞ b) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hu : Integrable u ν) (hbu : Integrable (fun y => b y * u y) ν) (x v : E) :
    fderiv ℝ (fun z => b z * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) z) x v =
      fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => b y * u y)) x v +
        fderiv ℝ (multiplicationMollifierCommutator ν b ρ u) x v := by
  have hprod : ContDiff ℝ ∞ (fun z => b z * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] u) z) :=
    hb.mul (hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hu.locallyIntegrable)
  have hconv : ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => b y * u y)) :=
    hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hbu.locallyIntegrable
  unfold multiplicationMollifierCommutator
  rw [fderiv_fun_sub (hprod.differentiable (by simp) x) (hconv.differentiable (by simp) x)]
  simp only [sub_apply]
  ring

/-- The actual divergence expression on a smooth finite vector field. -/
def divergenceSystemApply {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (U : E → α → ℝ) (x : E) (r : β) : ℝ :=
  ∑ c, (-(∑ i, ∑ j, fderiv ℝ (fun z => a r c i j z *
      fderiv ℝ (fun y => U y c) z (v j)) x (v i)) +
    (∑ i, fderiv ℝ (fun z => B r c i z * U z c) x (v i)) + C r c x * U x c)

/-- A finite divergence-form system tested in formal-transpose form.
Only the tests and coefficient fields are differentiated. -/
def divergenceSystemWeakEquation {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (u : E → α → ℝ) (F0 : E → β → ℝ) (F : E → β → ι → ℝ) : Prop :=
  ∀ (r : β) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∑ c, ((∑ i, ∑ j, -(∫ y,
      (a r c i j y * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) y (v j) +
        fderiv ℝ (a r c i j) y (v j) * fderiv ℝ φ y (v i)) * u y c ∂ν)) +
      (∑ i, -(∫ y, (B r c i y * fderiv ℝ φ y (v i)) * u y c ∂ν)) +
      ∫ y, φ y * (C r c y * u y c) ∂ν)) =
      (∫ y, φ y * F0 y r ∂ν) - ∑ i, ∫ y, fderiv ℝ φ y (v i) * F y r i ∂ν

/-- Testing the raw divergence equation against the translated genuine
kernel gives an exact smooth equation. No weak derivative of `u` is a
premise or is evaluated in the formula. -/
theorem divergenceSystemWeakEquation_mollified {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (u : E → α → ℝ) (F0 : E → β → ℝ) (F : E → β → ι → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ 1 (a r c i j))
    (hau : ∀ r c i j, Integrable (fun y => a r c i j y * u y c) ν)
    (hdau : ∀ r c i j, Integrable (fun y => fderiv ℝ (a r c i j) y (v j) * u y c) ν)
    (hBu : ∀ r c i, Integrable (fun y => B r c i y * u y c) ν)
    (hCu : ∀ r c, Integrable (fun y => C r c y * u y c) ν)
    (hF0 : ∀ r, Integrable (fun y => F0 y r) ν)
    (hF : ∀ r i, Integrable (fun y => F y r i) ν)
    (hweak : divergenceSystemWeakEquation ν v a B C u F0 F)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (r : β) (x : E) :
    (∑ c, ((∑ i, ∑ j,
      (-fderiv ℝ (fun z => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => a r c i j y * u y c)) z (v j)) x (v i) +
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => fderiv ℝ (a r c i j) y (v j) * u y c)) x (v i))) +
      (∑ i, fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
        (fun y => B r c i y * u y c)) x (v i)) +
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => C r c y * u y c)) x)) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F0 y r)) x +
        ∑ i, fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) x (v i) := by
  classical
  let φ : E → ℝ := fun y => ρ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hρ.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using hcρ.comp_homeomorph (Homeomorph.subLeft x)
  have hp (c : α) (i j : ι) :
      -(∫ y, (a r c i j y * fderiv ℝ (fun z => fderiv ℝ φ z (v i)) y (v j) +
        fderiv ℝ (a r c i j) y (v j) * fderiv ℝ φ y (v i)) * u y c ∂ν) =
      -fderiv ℝ (fun z => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => a r c i j y * u y c)) z (v j)) x (v i) +
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => fderiv ℝ (a r c i j) y (v j) * u y c)) x (v i) :=
    translated_kernel_principal_identity ν _ ρ _ (ha r c i j) hρ hcρ
      (v i) (v j) (hau r c i j) (hdau r c i j) x
  have hb (c : α) (i : ι) :
      -(∫ y, (B r c i y * fderiv ℝ φ y (v i)) * u y c ∂ν) =
        fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
          (fun y => B r c i y * u y c)) x (v i) := by
    rw [convolution_directional_derivative ν ρ _ (hρ.of_le (by simp)) hcρ (hBu r c i), ← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only [φ]
      rw [translated_kernel_derivative ρ hρ]
      ring
  have hc (c : α) : (∫ y, φ y * (C r c y * u y c) ∂ν) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => C r c y * u y c)) x := by
    rw [MeasureTheory.convolution_lsmul_swap]
    rfl
  have hf0 : (∫ y, φ y * F0 y r ∂ν) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F0 y r)) x := by
    rw [MeasureTheory.convolution_lsmul_swap]
    rfl
  have hf (i : ι) : -(∫ y, fderiv ℝ φ y (v i) * F y r i ∂ν) =
      fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) x (v i) := by
    rw [convolution_directional_derivative ν ρ _ (hρ.of_le (by simp)) hcρ (hF r i), ← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only [φ]
      rw [translated_kernel_derivative ρ hρ]
      ring
  have hw := hweak r φ hφ hcφ
  simp_rw [hp, hb, hc, hf0] at hw
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib] at hw
  simp_rw [hf] at hw
  exact hw

/-- The actual second-order residual consists of a zeroth-order
multiplication commutator and divergences of the already proved first-order
Friedrichs and multiplication commutators. In particular it does not
differentiate the raw input. -/
theorem divergenceSystemWeakEquation_mollifier_residual {α β ι : Type*}
    [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (u : E → α → ℝ) (F0 : E → β → ℝ) (F : E → β → ι → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hu : ∀ c, Integrable (fun y => u y c) ν)
    (hau : ∀ r c i j, Integrable (fun y => a r c i j y * u y c) ν)
    (hdau : ∀ r c i j, Integrable (fun y => fderiv ℝ (a r c i j) y (v j) * u y c) ν)
    (hBu : ∀ r c i, Integrable (fun y => B r c i y * u y c) ν)
    (hCu : ∀ r c, Integrable (fun y => C r c y * u y c) ν)
    (hF0 : ∀ r, Integrable (fun y => F0 y r) ν)
    (hF : ∀ r i, Integrable (fun y => F y r i) ν)
    (hweak : divergenceSystemWeakEquation ν v a B C u F0 F)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (r : β) (x : E) :
    divergenceSystemApply v a B C
        (fun z c => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => u y c)) z) x r =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F0 y r)) x +
        (∑ i, fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) x (v i)) +
        (∑ c, multiplicationMollifierCommutator ν (C r c) ρ (fun y => u y c) x) -
        (∑ c, ∑ i, ∑ j, fderiv ℝ
          (fun z => ∫ y, friedrichsCommutatorKernel (a r c i j) ρ (v j) z y * u y c ∂ν) x (v i)) +
        ∑ c, ∑ i, fderiv ℝ
          (multiplicationMollifierCommutator ν (B r c i) ρ (fun y => u y c)) x (v i) := by
  classical
  have hm := divergenceSystemWeakEquation_mollified ν v a B C u F0 F
    (fun r c i j => (ha r c i j).of_le (by simp)) hau hdau hBu hCu hF0 hF hweak ρ hρ hcρ r x
  have hp (c : α) (i j : ι) := friedrichsCommutatorKernel_flux_derivative ν
    (a r c i j) ρ (fun y => u y c) (ha r c i j) hρ hcρ (hu c) (hau r c i j)
    (v j) (hdau r c i j) x (v i)
  have hb (c : α) (i : ι) := multiplicationMollifierCommutator_derivative ν
    (B r c i) ρ (fun y => u y c) (hB r c i) hρ hcρ (hu c) (hBu r c i) x (v i)
  have hc (c : α) : C r c x * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => u y c)) x =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => C r c y * u y c)) x +
        multiplicationMollifierCommutator ν (C r c) ρ (fun y => u y c) x := by
    unfold multiplicationMollifierCommutator
    ring
  unfold divergenceSystemApply
  simp_rw [hp, hb, hc]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hm ⊢
  linarith

end Euclidean

end Yau.LeafProofs.L03
