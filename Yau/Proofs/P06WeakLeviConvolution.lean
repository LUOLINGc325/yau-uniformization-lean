import Yau.Proofs.P06LeviConvolution
import Yau.Proofs.P06WeakLeviSign

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint

theorem leviC_zero_off_tsupport {n : ℕ} (ρ : ComplexVector n → ℝ)
    {a : ComplexVector n} (ha : a ∉ tsupport ρ) : leviC ρ a = 0 := by
  have hg : ρ =ᶠ[𝓝 a] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport ρ).compl_mem_nhds ha] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq hg]
  ext i j
  simp [leviC, leviMatrix, wirt, wirtBar]

/-- A positive compact smoothing kernel transports the literal original
weak Levi test to the classical Hessian of its actual convolution.
The translated support and agreement of the L¹ extension are explicit. -/
theorem weakLeviUpper_convolution_direction {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (C : ℝ)
    (hw : WeakLeviUpper g.form f C) (x : M.Carrier)
    (ρ : ComplexVector n → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρnonneg : ∀ a, 0 ≤ ρ a) (F : ComplexVector n → ℝ) (hF : Integrable F volume)
    (z : ComplexVector n) (hFeq : ∀ a, z - a ∈ tsupport ρ → F a = inChart x f a)
    (hz : {a | z - a ∈ tsupport ρ} ⊆ chartTarget x) (v : ComplexVector n) :
    leviDirection (leviC (ρ ⋆[lsmul ℝ ℝ, volume] F) z) v ≤
      C * ∫ a, ρ (z - a) * leviDirection (hMat g.form x a) v := by
  let ψ : ComplexVector n → ℝ := fun a => ρ (z - a)
  have hψ : ContDiff ℝ ∞ ψ := hρ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := hcρ.comp_homeomorph (Homeomorph.subLeft z)
  have hsψ : tsupport ψ ⊆ chartTarget x := by
    change tsupport (ρ ∘ Homeomorph.subLeft z) ⊆ chartTarget x
    rw [tsupport_comp_eq_preimage]
    exact hz
  obtain ⟨_, _, hineq⟩ := hw x v ψ hψ hcψ hsψ (fun a => hρnonneg (z - a))
  rw [Yau.LeafProofs.lebesgueC_eq_volume] at hineq
  have heq : (∫ a, inChart x f a * leviDirection (leviC ψ a) v) =
      leviDirection (leviC (ρ ⋆[lsmul ℝ ℝ, volume] F) z) v := by
    rw [convolution_leviDirection ρ F hρ hcρ hF z v]
    apply integral_congr_ae
    filter_upwards [] with a
    rw [leviDirection_reflect ρ hρ z v a]
    by_cases ha : z - a ∈ tsupport ρ
    · rw [hFeq a ha]
      ring
    · rw [leviC_zero_off_tsupport ρ ha]
      simp only [leviDirection, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re,
        mul_zero, zero_mul]
  rw [heq] at hineq
  exact hineq

end Yau.NodeProofs.P06Aux
