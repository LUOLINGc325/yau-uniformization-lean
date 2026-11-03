import Yau.Proofs.V03AngularDirichlet
import Yau.Proofs.V03RealTraceDerivative

/-! Actual real parameter jets of a smooth periodic boundary family,
including their genuine uniform compact traces. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

def realParameterDerivative (f : ℂ × ℝ → ℂ) (v : ℂ) (p : ℂ × ℝ) : ℂ :=
  fderiv ℝ f p (v, 0)

theorem realParameterDerivative_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) (v : ℂ) :
    ContDiffOn ℝ ∞ (realParameterDerivative f v) (U ×ˢ Set.univ) :=
  (hf.fderiv_of_isOpen (hU.prod isOpen_univ) (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem realParameterDerivative_eq_slice {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) (θ : ℝ) :
    realParameterDerivative f v (z, θ) = fderiv ℝ (fun p => f (p, θ)) z v := by
  have hmem : U ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 (z, θ) :=
    (hU.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ θ⟩
  rw [fderiv_spatial_slice hU hz (Set.mem_univ θ)
    ((hf.differentiableOn (by simp)) _ ⟨hz, Set.mem_univ θ⟩) v,
    fderivWithin_of_mem_nhds hmem]
  rfl

theorem realParameterDerivative_periodic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    Function.Periodic (fun θ => realParameterDerivative f v (z, θ)) (2 * Real.pi) := by
  intro θ
  dsimp only
  rw [realParameterDerivative_eq_slice hU hf hz, realParameterDerivative_eq_slice hU hf hz]
  have he : (fun p => f (p, θ + 2 * Real.pi)) =ᶠ[𝓝 z] (fun p => f (p, θ)) := by
    filter_upwards [hU.mem_nhds hz] with p hpU
    exact hp p hpU θ
  exact congrArg (fun A : ℂ →L[ℝ] ℂ => A v) he.fderiv_eq

def realFamilyUniformTrace {U : Set ℂ} {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) (z : ℂ) : C(BoundaryAngleInterval, ℂ) :=
  compactParamTrace ((hf.mono (show U ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ U ×ˢ Set.univ from
    fun p hp => ⟨hp.1, Set.mem_univ _⟩)).continuousOn) z

theorem realFamilyUniformTrace_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (realFamilyUniformTrace hf) U :=
  compactParamTrace_contDiffOn hU (uniqueDiffOn_Icc (by positivity))
    (hf.mono (fun p hp => ⟨hp.1, Set.mem_univ _⟩))

theorem realFamilyUniformTrace_apply {U : Set ℂ}
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    {z : ℂ} (hz : z ∈ U) (θ : BoundaryAngleInterval) :
    realFamilyUniformTrace hf z θ = f (z, θ) :=
  compactParamTrace_apply _ hz θ

theorem fderiv_realFamilyUniformTrace_apply {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    {z : ℂ} (hz : z ∈ U) (v : ℂ) (θ : BoundaryAngleInterval) :
    fderiv ℝ (realFamilyUniformTrace hf) z v θ = realParameterDerivative f v (z, θ) := by
  have hT : DifferentiableAt ℝ (realFamilyUniformTrace hf) z :=
    ((realFamilyUniformTrace_contDiffOn hU hf).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  rw [fderiv_real_continuousMap_eval hT v θ, realParameterDerivative_eq_slice hU hf hz]
  have he : (fun p => realFamilyUniformTrace hf p θ) =ᶠ[𝓝 z] (fun p => f (p, θ)) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact realFamilyUniformTrace_apply hf hp θ
  exact congrArg (fun A : ℂ →L[ℝ] ℂ => A v) he.fderiv_eq

end Yau.Blueprint.V03Proof
