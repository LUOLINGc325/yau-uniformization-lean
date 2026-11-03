import Yau.Proofs.V03RealDirichletDerivative
import Yau.Proofs.V03HilbertQuadratic

/-! The actual mixed derivative of a real periodic boundary seminorm
is controlled by its actual first jets and its actual Laplacian jet. -/

open scoped Topology ContDiff lp

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem angularDirichletVector_add {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hg : ContDiffOn ℝ ∞ g (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U)
    (hfp : Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    (hgp : Function.Periodic (fun θ => g (z, θ)) (2 * Real.pi)) :
    angularDirichletVector hU (hf.add hg) z =
      angularDirichletVector hU hf z + angularDirichletVector hU hg z := by
  apply Subtype.ext
  funext k
  change angularDirichletVector hU (hf.add hg) z k =
    angularDirichletVector hU hf z k + angularDirichletVector hU hg z k
  rw [angularDirichletVector_coeff hU (hf.add hg) hz (hfp.add hgp),
    angularDirichletVector_coeff hU hf hz hfp, angularDirichletVector_coeff hU hg hz hgp,
    dirichletCoeff, circleFourier_add (parameter_angle_slice_contDiff hf hz).continuous
      (parameter_angle_slice_contDiff hg hz).continuous, mul_add]
  rfl

theorem angularDirichletVector_const_mul {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U)
    (hp : Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi)) (c : ℂ) :
    angularDirichletVector hU ((contDiffOn_const (c := c)).mul hf) z =
      c • angularDirichletVector hU hf z := by
  apply Subtype.ext
  funext k
  change angularDirichletVector hU ((contDiffOn_const (c := c)).mul hf) z k =
    c * angularDirichletVector hU hf z k
  rw [angularDirichletVector_coeff hU ((contDiffOn_const (c := c)).mul hf) hz
      (fun θ => congrArg (c * ·) (hp θ)),
    angularDirichletVector_coeff hU hf hz hp, dirichletCoeff, circleFourier_const_mul]
  unfold dirichletCoeff
  ring

def realParameterLaplacian (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  realParameterDerivative (realParameterDerivative f 1) 1 p +
    realParameterDerivative (realParameterDerivative f Complex.I) Complex.I p

theorem realParameterLaplacian_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (realParameterLaplacian f) (U ×ˢ Set.univ) :=
  (realParameterDerivative_contDiffOn hU (realParameterDerivative_contDiffOn hU hf 1) 1).add
    (realParameterDerivative_contDiffOn hU (realParameterDerivative_contDiffOn hU hf Complex.I) Complex.I)

theorem realParameterLaplacian_periodic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {z : ℂ} (hz : z ∈ U) :
    Function.Periodic (fun θ => realParameterLaplacian f (z, θ)) (2 * Real.pi) :=
  (realParameterDerivative_periodic hU (realParameterDerivative_contDiffOn hU hf 1)
    (fun p hpU => realParameterDerivative_periodic hU hf hp hpU 1) hz 1).add
  (realParameterDerivative_periodic hU (realParameterDerivative_contDiffOn hU hf Complex.I)
    (fun p hpU => realParameterDerivative_periodic hU hf hp hpU Complex.I) hz Complex.I)

theorem laplacian_realAngularDirichletVector {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi))
    {z : ℂ} (hz : z ∈ U) :
    fderiv ℝ (fderiv ℝ (angularDirichletVector hU hf)) z 1 1 +
      fderiv ℝ (fderiv ℝ (angularDirichletVector hU hf)) z Complex.I Complex.I =
        angularDirichletVector hU (realParameterLaplacian_contDiffOn hU hf) z := by
  rw [secondFDeriv_realAngularDirichletVector hU hf hp hz,
    secondFDeriv_realAngularDirichletVector hU hf hp hz]
  symm
  exact angularDirichletVector_add hU _ _ hz
    (realParameterDerivative_periodic hU (realParameterDerivative_contDiffOn hU hf 1)
      (fun p hpU => realParameterDerivative_periodic hU hf hp hpU 1) hz 1)
    (realParameterDerivative_periodic hU (realParameterDerivative_contDiffOn hU hf Complex.I)
      (fun p hpU => realParameterDerivative_periodic hU hf hp hpU Complex.I) hz Complex.I)

theorem realAngularDirichlet_norm {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U)
    (hp : Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi)) :
    ‖angularDirichletVector hU hf z‖ =
      Real.sqrt (boundaryDSq (fun θ (_ : Unit) => f (z, θ))).toReal := by
  rw [← angularDirichletVector_norm_sq hU hf hz hp, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

theorem abs_mixedReal_boundaryDSq_le_actual_jets {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ × ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (U ×ˢ Set.univ))
    (hp : ∀ z ∈ U, Function.Periodic (fun θ => g (z, θ)) (2 * Real.pi))
    (h0 : (0 : ℂ) ∈ U) :
    let f : ℂ × ℝ → ℂ := fun p => (g p : ℂ)
    |mixedReal (fun z => (boundaryDSq (fun θ (_ : Unit) => f (z, θ))).toReal)| ≤
      (1 / 2 : ℝ) * ((boundaryDSq (fun θ (_ : Unit) => realParameterDerivative f 1 (0, θ))).toReal +
        (boundaryDSq (fun θ (_ : Unit) => realParameterDerivative f Complex.I (0, θ))).toReal) +
      (1 / 2 : ℝ) * Real.sqrt (boundaryDSq (fun θ (_ : Unit) => f (0, θ))).toReal *
        Real.sqrt (boundaryDSq (fun θ (_ : Unit) => realParameterLaplacian f (0, θ))).toReal := by
  let f : ℂ × ℝ → ℂ := fun p => (g p : ℂ)
  dsimp only
  have hf : ContDiffOn ℝ ∞ f (U ×ˢ Set.univ) := Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  have hfp : ∀ z ∈ U, Function.Periodic (fun θ => f (z, θ)) (2 * Real.pi) :=
    fun z hz θ => congrArg Complex.ofReal (hp z hz θ)
  let Q := angularDirichletVector hU hf
  have hQ : ContDiffAt ℝ 2 Q 0 :=
    ((angularDirichletVector_contDiffOn hU hf).contDiffAt (hU.mem_nhds h0)).of_le (by simp)
  have heq : (fun z => (boundaryDSq (fun θ (_ : Unit) => f (z, θ))).toReal) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => ‖Q z‖ ^ 2) := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact (angularDirichletVector_norm_sq hU hf hz (hfp z hz)).symm
  rw [mixedReal_congr heq]
  have hb := abs_mixedReal_norm_sq_le hQ
  have hD1 : ‖fderiv ℝ Q 0 1‖ ^ 2 =
      (boundaryDSq (fun θ (_ : Unit) => realParameterDerivative f 1 (0, θ))).toReal :=
    fderiv_realAngularDirichletVector_norm_sq hU hf hfp h0 (1 : ℂ)
  have hDI : ‖fderiv ℝ Q 0 Complex.I‖ ^ 2 =
      (boundaryDSq (fun θ (_ : Unit) => realParameterDerivative f Complex.I (0, θ))).toReal :=
    fderiv_realAngularDirichletVector_norm_sq hU hf hfp h0 Complex.I
  rw [hD1, hDI] at hb
  dsimp only [Q] at hb
  rw [laplacian_realAngularDirichletVector hU hf hfp h0,
    realAngularDirichlet_norm hU hf h0 (hfp 0 h0),
    realAngularDirichlet_norm hU (realParameterLaplacian_contDiffOn hU hf) h0
      (realParameterLaplacian_periodic hU hf hfp h0)] at hb
  exact hb

end Yau.Blueprint.V03Proof
