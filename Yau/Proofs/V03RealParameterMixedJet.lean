import Yau.Proofs.V03RealDirichletMixed
import Yau.Proofs.V03LeviChain

/-! The actual joint Laplacian jet equals four times the actual nested
mixed derivative of each real boundary slice. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem secondRealParameterDerivative_eq_slice {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    {z : ℂ} (hz : z ∈ U) (v w : ℂ) (θ : ℝ) :
    realParameterDerivative (realParameterDerivative f v) w (z, θ) =
      fderiv ℝ (fderiv ℝ (fun p => f (p, θ))) z w v := by
  have hs : ContDiffOn ℝ ∞ (fun p => f (p, θ)) U :=
    hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun p hp => ⟨hp, Set.mem_univ θ⟩)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun p => f (p, θ))) z :=
    (((hs.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by simp))).differentiableAt one_ne_zero
  rw [realParameterDerivative_eq_slice hU (realParameterDerivative_contDiffOn hU hf v) hz]
  have he : (fun p => realParameterDerivative f v (p, θ)) =ᶠ[𝓝 z]
      (fun p => fderiv ℝ (fun p' => f (p', θ)) p v) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact realParameterDerivative_eq_slice hU hf hp v θ
  rw [he.fderiv_eq]
  exact (fderiv_real_clm_apply hd w v).symm

theorem realParameterLaplacian_ofReal_eq_four_mixed {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ × ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (U ×ˢ Set.univ))
    (h0 : (0 : ℂ) ∈ U) (θ : ℝ) :
    realParameterLaplacian (fun p => (g p : ℂ)) (0, θ) =
      (4 : ℂ) * (mixedReal (fun z => g (z, θ)) : ℂ) := by
  have hf : ContDiffOn ℝ ∞ (fun p => (g p : ℂ)) (U ×ˢ Set.univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  have hs : ContDiffAt ℝ 2 (fun p => g (p, θ)) 0 :=
    ((hg.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun p hp => ⟨hp, Set.mem_univ θ⟩)).contDiffAt (hU.mem_nhds h0)).of_le (by simp)
  rw [realParameterLaplacian, secondRealParameterDerivative_eq_slice hU hf h0,
    secondRealParameterDerivative_eq_slice hU hf h0,
    secondFDeriv_ofReal hs, secondFDeriv_ofReal hs]
  unfold mixedReal
  rw [mixedWirt_real_diagonal hs]
  simp only [smul_eq_mul, mul_one, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

end Yau.Blueprint.V03Proof
