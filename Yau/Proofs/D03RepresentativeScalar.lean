import Yau.Proofs.B01Coordinate
import Yau.LeafProofs.L21ClassicalEquation
import Yau.LeafProofs.L14Exact
import Mathlib.Analysis.Complex.Conformal

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint.BundlePresentation
open Yau.LeafProofs.L21Aux

/-- The ordinary Cauchy--Riemann implication on the actual one-dimensional
model space, for the frozen real Frechet Wirtinger derivative. -/
theorem differentiableAt_of_wirtBar_eq_zero
    {f : ComplexVector 1 → ℂ} {x : ComplexVector 1}
    (hf : DifferentiableAt ℝ f x) (hbar : wirtBar f x (stdVec 0) = 0) :
    DifferentiableAt ℂ f x := by
  let e : ℂ ≃L[ℂ] ComplexVector 1 := B01Aux.complexOneEquiv.toContinuousLinearEquiv
  let z := e.symm x
  let F : ℂ → ℂ := f ∘ e
  have he1 : e 1 = stdVec 0 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [e, B01Aux.complexOneEquiv_apply, stdVec, PiLp.single_apply]
  have heI : e Complex.I = Complex.I • stdVec 0 := by
    rw [← he1, ← map_smul]
    simp
  have heR : DifferentiableAt ℝ e z := e.differentiableAt.restrictScalars ℝ
  have hx : e z = x := e.apply_symm_apply x
  have hfz : DifferentiableAt ℝ f (e z) := hx.symm ▸ hf
  have hFR : DifferentiableAt ℝ F z := hfz.comp z heR
  have hD : fderiv ℝ F z = (fderiv ℝ f x).comp
      (e.toContinuousLinearMap.restrictScalars ℝ) := by
    have heFD : fderiv ℝ e z = e.toContinuousLinearMap.restrictScalars ℝ :=
      (e.toContinuousLinearMap.hasFDerivAt.restrictScalars ℝ).fderiv
    change fderiv ℝ (f ∘ e) z = _
    rw [fderiv_comp z hfz heR, hx, heFD]
  have hsum : fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I = 0 := by
    have hbar' : (1 / 2 : ℂ) *
        (fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I) = 0 := by
      rw [hD]
      change (1 / 2 : ℂ) * (fderiv ℝ f x (e 1) +
        Complex.I * fderiv ℝ f x (e Complex.I)) = 0
      rw [he1, heI]
      exact hbar
    exact (mul_eq_zero.mp hbar').resolve_left (by norm_num)
  have hCR : fderiv ℝ F z Complex.I = Complex.I • fderiv ℝ F z 1 := by
    simp only [smul_eq_mul]
    have hmul : Complex.I * fderiv ℝ F z 1 - fderiv ℝ F z Complex.I = 0 := by
      have hm := congrArg (Complex.I * ·) hsum
      simpa only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
        ← sub_eq_add_neg, mul_zero] using hm
    exact (sub_eq_zero.mp hmul).symm
  have hFC : DifferentiableAt ℂ F z :=
    differentiableAt_complex_iff_differentiableAt_real.mpr ⟨hFR, hCR⟩
  have hback := hFC.comp x e.symm.differentiableAt
  simpa only [F, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hback

/-- The zero graph's transpose is precisely the scalar weak dbar test. -/
theorem transposeRow_zero (ψ : ComplexVector 1 → ℝ) (hψ : Differentiable ℝ ψ)
    (x : ComplexVector 1) :
    transposeRow (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) 0 ψ x =
      -wirtBar (fun y => (ψ y : ℂ)) x (stdVec 0) := by
  have hcoeff (a : Yau.RIdx 1) :
      dbarRealCoefficient (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) 0 a =
        fun _ => wirtBarRealCoefficient a.2 := by
    funext y
    have ha : a.1 = 0 := Subsingleton.elim _ _
    simp [dbarRealCoefficient, ha]
  rw [wirtBar_eq_real_directions]
  simp only [transposeRow, hcoeff, fderiv_const, _root_.zero_apply,
    zero_mul, add_zero, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two,
    fderiv_ofReal_apply (hψ x)]
  norm_num [wirtBarRealCoefficient]

/-- The accepted L21 regularity infrastructure, specialized to zero graph and
zero source, provides a holomorphic representative on every compactly contained
open subdomain. It retains equality to the original weak coefficient a.e. -/
theorem exists_inner_holomorphic_of_weak_dbar_zero
    {O R : Set (ComplexVector 1)} (hO : IsOpen O)
    (u : ComplexVector 1 → ℂ) (hu : LocallyL2On u O)
    (hweak : ∀ (ψ : ComplexVector 1 → ℂ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ O →
      (∫ x, u x * wirtBar ψ x (stdVec 0) ∂Yau.lebesgueC 1) = 0)
    (hR : IsOpen R) (hcR : IsCompact (closure R)) (hRO : closure R ⊆ O) :
    ∃ v : ComplexVector 1 → ℂ, ContDiff ℝ ∞ v ∧
      DifferentiableOn ℂ v R ∧ v =ᵐ[(Yau.lebesgueC 1).restrict R] u := by
  let A : ComplexVector 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 0
  have hA : MatrixSmoothOn A O := fun _ _ => contDiffOn_const
  have hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2 := by
    intro x hx
    simp [A, Yau.LeafCandidates.matrixOpNorm]
  have heq : DbarWeakOn A u (fun _ _ => 0) O := by
    intro i ψ hψ hcψ hsψ
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hcψC : HasCompactSupport (fun x => (ψ x : ℂ)) :=
      hcψ.comp_left Complex.ofReal_zero
    have hsψC : tsupport (fun x => (ψ x : ℂ)) ⊆ O :=
      (tsupport_comp_subset Complex.ofReal_zero ψ).trans hsψ
    have ht := hweak (fun x => (ψ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hψ) hcψC hsψC
    simp only [mul_zero, integral_zero]
    simp only [A, transposeRow_zero ψ (hψ.differentiable (by simp)), mul_neg,
      integral_neg, ht, neg_zero]
  obtain ⟨v, hv, hvu, hvbar⟩ := exists_inner_smooth_solution hO hA hsmall
    (fun _ _ => 0) (fun _ => contDiffOn_const) u hu heq hR hcR hRO
  refine ⟨v, hv, ?_, hvu⟩
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_of_wirtBar_eq_zero (hv.differentiable (by simp) x)
  simpa [dbarA, A] using hvbar x hx 0

section OriginalBundle
open BundleDbar

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Apply scalar regularity to the exact weak coefficient of the original
bundle top form, with its original local frame and measure. -/
theorem exists_inner_holomorphic_top_coefficient
    (W : NQForm E 0) (hW : WeakDbar (r := r) E W 0)
    (a : M.Carrier) (α : Fin r) {R : Set (ComplexVector 1)}
    (hR : IsOpen R) (hcR : IsCompact (closure R))
    (hRO : closure R ⊆ localDomain (r := r) E a) :
    ∃ v : ComplexVector 1 → ℂ, ContDiff ℝ ∞ v ∧
      DifferentiableOn ℂ v R ∧
      v =ᵐ[(Yau.lebesgueC 1).restrict R]
        (fun z => coefficients (r := r) E W a z Fin.elim0 α) := by
  apply exists_inner_holomorphic_of_weak_dbar_zero
    (Yau.LeafProofs.L14Aux.localDomain_isOpen (r := r) E a)
    (fun z => coefficients (r := r) E W a z Fin.elim0 α)
  · intro K hK hKO
    exact Yau.LeafProofs.L14Aux.locallyL2_coefficients_memLp (r := r) E W hW.1 a Fin.elim0 α K hK hKO
  · intro ψ hψ hcψ hsψ
    have ht := ((Yau.LeafProofs.L14Aux.weakDbar_zero_iff_component_tests
      (r := r) E W (0 : NQForm E 1)).mp hW).2.2 a 0 α ψ hψ hcψ hsψ
    simpa only [Yau.LeafProofs.L14Aux.coefficients_zero (r := r) E,
      zero_mul, integral_zero, neg_eq_zero] using ht.symm
  · exact hR
  · exact hcR
  · exact hRO

end OriginalBundle

end Yau.Proofs.D03Aux
