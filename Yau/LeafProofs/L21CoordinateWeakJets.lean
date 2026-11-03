import Yau.LeafProofs.L21RealCoordinates
import Yau.LeafProofs.L16CoordinateRegularity

/-! Genuine weak coordinate jets transfer through the volume-preserving
real coordinates and every actual real linear component of a complex scalar. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem realCLM_mul_ofReal (ℓ : ℂ →L[ℝ] ℝ) (z : ℂ) (r : ℝ) :
    ℓ (z * (r : ℂ)) = ℓ z * r := by
  simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using ℓ.map_smul r z

theorem realCLM_weak_derivative (ℓ : ℂ →L[ℝ] ℝ) {u g : X n → ℂ} {v : X n}
    (hu : MemLp u 2 (Yau.lebesgueC n)) (hg : MemLp g 2 (Yau.lebesgueC n))
    (hWeak : ComplexWeakDerivative u g v)
    (ψ : X n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, ℓ (u x) * fderiv ℝ ψ x v ∂Yau.lebesgueC n) =
      -(∫ x, ℓ (g x) * ψ x ∂Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have hψC : MemLp (fun x => (ψ x : ℂ)) 2 (Yau.lebesgueC n) :=
    (Complex.ofRealCLM.continuous.comp hψ.continuous).memLp_of_hasCompactSupport
      (hcψ.comp_left Complex.ofReal_zero)
  have hDψ := (hψ.fderiv_right (m := ∞) (by simp)).clm_apply
    (show ContDiff ℝ ∞ (fun _ : X n => v) from contDiff_const)
  have hDψC : MemLp (fun x => (fderiv ℝ ψ x v : ℂ)) 2 (Yau.lebesgueC n) :=
    (Complex.ofRealCLM.continuous.comp hDψ.continuous).memLp_of_hasCompactSupport
      ((hcψ.fderiv_apply ℝ v).comp_left Complex.ofReal_zero)
  have hIntU : Integrable (fun x => u x * (fderiv ℝ ψ x v : ℂ)) (Yau.lebesgueC n) :=
    hu.integrable_mul hDψC
  have hIntG : Integrable (fun x => g x * (ψ x : ℂ)) (Yau.lebesgueC n) := hg.integrable_mul hψC
  have hh := congrArg ℓ (hWeak ψ hψ hcψ)
  rw [← ℓ.integral_comp_comm hIntU, map_neg, ← ℓ.integral_comp_comm hIntG] at hh
  simpa only [realCLM_mul_ofReal] using hh

theorem complexWeakDerivative_realCoordinates (ℓ : ℂ →L[ℝ] ℝ)
    {u g : X n → ℂ} (hu : MemLp u 2 (Yau.lebesgueC n)) (hg : MemLp g 2 (Yau.lebesgueC n))
    (j : Fin (realDimension n))
    (hWeak : ComplexWeakDerivative u g (Yau.realVec ((realIndex n).symm j)))
    (φ : (Fin (realDimension n) → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ y, ℓ (u ((realCoordinates n).symm y)) * fderiv ℝ φ y (Pi.single j 1)) =
      -(∫ y, ℓ (g ((realCoordinates n).symm y)) * φ y) := by
  have hψ : ContDiff ℝ ∞ (φ ∘ realCoordinates n) := hφ.comp (realCoordinates n).contDiff
  have hcψ : HasCompactSupport (φ ∘ realCoordinates n) := hcφ.comp_homeomorph (realCoordinates n).toHomeomorph
  have hh := realCLM_weak_derivative ℓ hu hg hWeak _ hψ hcψ
  simp only [realCoordinates_directional (hφ.differentiable (by simp)), Equiv.apply_symm_apply,
    Function.comp_apply] at hh
  have h1 := (realCoordinates_symm_measurePreserving n).integral_comp
    (realCoordinates n).symm.toHomeomorph.measurableEmbedding
    (fun x => ℓ (u x) * fderiv ℝ φ (realCoordinates n x) (Pi.single j 1))
  have h2 := (realCoordinates_symm_measurePreserving n).integral_comp
    (realCoordinates n).symm.toHomeomorph.measurableEmbedding (fun x => ℓ (g x) * φ (realCoordinates n x))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h1 h2
  exact h1.trans (hh.trans (congrArg Neg.neg h2.symm))

def realCoordinateJet (ℓ : ℂ →L[ℝ] ℝ) (U : List (Yau.RIdx n) → X n → ℂ)
    (w : List (Fin (realDimension n))) (y : Fin (realDimension n) → ℝ) : ℝ :=
  ℓ (U (w.map (realIndex n).symm) ((realCoordinates n).symm y))

theorem finiteComplexWeakJet_realCoordinates (ℓ : ℂ →L[ℝ] ℝ) (N : ℕ)
    (u : X n → ℂ) (U : List (Yau.RIdx n) → X n → ℂ) (hJet : FiniteComplexWeakJet N u U) :
    Yau.LeafProofs.L16Aux.FiniteCoordinateWeakJet N
      (fun y => ℓ (u ((realCoordinates n).symm y))) (realCoordinateJet ℓ U) := by
  refine ⟨?_, ?_, ?_⟩
  · funext y
    change ℓ (U [] ((realCoordinates n).symm y)) = _
    rw [hJet.1]
  · intro w hw
    have hlen : (w.map (realIndex n).symm).length ≤ N := by simpa only [List.length_map] using hw
    have hU := hJet.2.1 _ hlen
    refine ⟨?_, ?_⟩
    · exact ℓ.comp_memLp' (hU.1.comp_measurePreserving (realCoordinates_symm_measurePreserving n))
    · exact (hU.2.comp_homeomorph (realCoordinates n).symm.toHomeomorph).comp_left (map_zero ℓ)
  · intro w hw j φ hφ hcφ
    have hlen : (w.map (realIndex n).symm).length < N := by simpa only [List.length_map] using hw
    have hcons : (((realIndex n).symm j) :: w.map (realIndex n).symm).length ≤ N := by
      simp only [List.length_cons]
      omega
    exact complexWeakDerivative_realCoordinates ℓ (hJet.2.1 _ hlen.le).1 (hJet.2.1 _ hcons).1 j
      (hJet.2.2 _ hlen _) φ hφ hcφ

end Yau.LeafProofs.L21Aux
