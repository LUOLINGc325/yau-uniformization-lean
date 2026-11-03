import Yau.Proofs.F03GaussianReferenceTransfer

/-! The actual left kernel gradient has a common reference Gaussian on compact spatial neighborhoods. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernelCandidate_left_gradient_single_center
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (b : ℝ),0 < b → ∀ x y,
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z y) x) ≤
        C/Real.sqrt b*Real.exp (-c*distFrom X.metric.form x y^2/b)/
          (μ (distBall X.metric.form x (Real.sqrt b))).toReal := by
  obtain ⟨_K,_d,C,c,_hK,_hd,hC,hc,hBound⟩ :=
    dirichletMinimalKernelCandidate_gaussian_gradient X o h U P ρ hf
  refine ⟨C*Real.exp ((n:ℝ)^2/(2*c)),c/2,by positivity,by positivity,?_⟩
  intro μ hμ O hO b hb x y
  have hInput : Real.sqrt (gradNormSq X.metric.form (fun z =>
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z y) x) ≤
      (C/Real.sqrt b)*Real.exp (-c*distFrom X.metric.form x y^2/(Real.sqrt b)^2)/
        Real.sqrt ((μ (distBall X.metric.form x (Real.sqrt b))).toReal*
          (μ (distBall X.metric.form y (Real.sqrt b))).toReal) := by
    simpa only [Real.sq_sqrt hb.le] using (hBound μ hμ O hO b hb x y).2
  have hSingle := symmetric_gaussian_to_single_center X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ x y (Real.sqrt_pos.mpr hb)
    (show 0 ≤ C/Real.sqrt b by positivity) hc hInput
  rw [Real.sq_sqrt hb.le] at hSingle
  convert hSingle using 1 <;> ring

theorem dirichletMinimalKernelCandidate_left_gradient_coarse_gaussian
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (L : ℝ),1 ≤ L →
      ∀ b : ℝ,0 < b → b ≤ L^2 → ∀ x,inducedDistance X.metric.form o x ≤ C₀*L → ∀ y,
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z y) x) ≤
        C/Real.sqrt b*(L/Real.sqrt b)^(2*n)*
          Real.exp (-c*(inducedDistance X.metric.form o y/((C₀+1)*L))^2)/
          (μ (distBall X.metric.form o ((C₀+1)*L))).toReal := by
  obtain ⟨K,c,hK,hc,hBound⟩ := dirichletMinimalKernelCandidate_left_gradient_single_center X o h U P ρ hf
  refine ⟨K*Real.exp c*(2*(C₀+1))^(2*n),c/2,by positivity,by positivity,?_⟩
  intro μ hμ O hO L hL b hb hbL x hx y
  have hInput : Real.sqrt (gradNormSq X.metric.form (fun z =>
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z y) x) ≤
      (K/Real.sqrt b)*Real.exp (-c*inducedDistance X.metric.form x y^2/b)/
        (μ (distBall X.metric.form x (Real.sqrt b))).toReal := hBound μ hμ O hO b hb x y
  have hCoarse := single_center_gaussian_to_reference X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ o x y hC₀
    (show 0 ≤ K/Real.sqrt b by positivity) hc hL hb hbL hx hInput
  convert hCoarse using 1 <;> ring

end Yau.Proofs.F03Aux
