import Yau.Proofs.V03CompactParamSmoothness
import Yau.Proofs.V03LogTrace

/-! The actual angular derivative has smooth parameter dependence in the
uniform norm on the full closed boundary-angle interval. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

def angularDerivative {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : P × ℝ → F) (p : P × ℝ) : F :=
  fderiv ℝ f p (0, 1)

theorem angularDerivative_contDiffOn {P F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set P} (hU : IsOpen U) {f : P × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (angularDerivative f) (U ×ˢ Set.univ) :=
  (hf.fderiv_of_isOpen (hU.prod isOpen_univ) (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem angularDerivative_hasDerivAt {P F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set P} (hU : IsOpen U) {f : P × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) {z : P} (hz : z ∈ U) (θ : ℝ) :
    HasDerivAt (fun t => f (z, t)) (angularDerivative f (z, θ)) θ := by
  have hAt : ContDiffAt ℝ ∞ f (z, θ) :=
    hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds
      (show (z, θ) ∈ U ×ˢ Set.univ from ⟨hz, Set.mem_univ θ⟩))
  have hline : HasDerivAt (fun t : ℝ => (z, t)) ((0 : P), 1) θ :=
    (hasDerivAt_const (x := θ) (c := z)).prodMk (hasDerivAt_id θ)
  simpa only [Function.comp_def, angularDerivative] using
    (hAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt θ hline

def angularCompactTrace {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) (z : ℂ) :
    C(Set.Icc (0 : ℝ) (2 * Real.pi), ℂ) :=
  compactParamTrace (((angularDerivative_contDiffOn hU hf).mono
    (show U ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ U ×ˢ Set.univ from
      fun p hp => ⟨hp.1, Set.mem_univ _⟩)).continuousOn) z

theorem angularCompactTrace_contDiffOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (angularCompactTrace hU hf) U := by
  exact compactParamTrace_contDiffOn hU (uniqueDiffOn_Icc (by positivity))
    ((angularDerivative_contDiffOn hU hf).mono (fun p hp => ⟨hp.1, Set.mem_univ _⟩))

theorem angularCompactTrace_apply {U : Set ℂ} (hU : IsOpen U) {f : ℂ × ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U)
    (θ : Set.Icc (0 : ℝ) (2 * Real.pi)) :
    angularCompactTrace hU hf z θ = deriv (fun t => f (z, t)) θ := by
  rw [angularCompactTrace, compactParamTrace_apply _ hz θ]
  exact (angularDerivative_hasDerivAt hU hf hz θ).deriv.symm

end Yau.Blueprint.V03Proof
