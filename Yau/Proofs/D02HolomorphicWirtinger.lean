import Yau.Proofs.D02BochnerAlgebra

/-! Holomorphic differentiation supplies the vanishing mixed term in the
dual Bochner calculation. This is proved from holomorphicity itself. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint.V03Proof Yau.LeafProofs.L14Aux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wirt_complex_eq_fderiv (f : V → ℂ) (z v : V) (hf : DifferentiableAt ℂ f z) :
    wirt f z v = fderiv ℂ f z v := by
  unfold wirt
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1 / 2 : ℂ) * (fderiv ℂ f z v - Complex.I * fderiv ℂ f z (Complex.I • v)) = _
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring

variable [FiniteDimensional ℂ V]

theorem wirt_holomorphic_differentiableOn {U : Set V} (hU : IsOpen U)
    {f : V → ℂ} (hf : DifferentiableOn ℂ f U) (v : V) :
    DifferentiableOn ℂ (fun w => wirt f w v) U := by
  apply (complex_holomorphic_fderiv_apply_differentiableOn hU hf v).congr
  intro w hw
  exact wirt_complex_eq_fderiv f w v ((hf w hw).differentiableAt (hU.mem_nhds hw))

theorem vectorWirtBar_holomorphic_zero {r : ℕ} {U : Set V} (hU : IsOpen U)
    (η : V → Fin r → ℂ) (hη : ∀ a, DifferentiableOn ℂ (fun w => η w a) U)
    (z v : V) (hz : z ∈ U) : vectorWirtBar η z v = 0 := by
  funext a
  exact wirtBar_eq_zero_of_complex_differentiable _ z v
    ((hη a z hz).differentiableAt (hU.mem_nhds hz))

theorem vectorWirtBar_vectorWirt_holomorphic_zero {r : ℕ} {U : Set V} (hU : IsOpen U)
    (η : V → Fin r → ℂ) (hη : ∀ a, DifferentiableOn ℂ (fun w => η w a) U)
    (z v : V) (hz : z ∈ U) :
    vectorWirtBar (fun w => vectorWirt η w v) z v = 0 := by
  apply vectorWirtBar_holomorphic_zero hU (fun w => vectorWirt η w v) _ z v hz
  intro a
  exact wirt_holomorphic_differentiableOn hU (hη a) v

end Yau.NodeProofs.D02Aux
