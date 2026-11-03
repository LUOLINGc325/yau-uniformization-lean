import Yau.LeafProofs.L23TensorMultilinear
import Yau.LeafProofs.L23FieldMetricConnection

/-! Local pullback calculus for the actual covariant tensor derivative. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

theorem linearMap_map_update (J : ComplexVector n →L[ℝ] ComplexVector n)
    (V : Fin r → ComplexVector n) (s : Fin r) (u : ComplexVector n) :
    (fun j => J (Function.update V s u j))=
      Function.update (fun j => J (V j)) s (J u) := by
  funext j
  by_cases hjs : j=s
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hjs]

theorem apply_update_linearMaps
    (J K : Fin r → ComplexVector n →L[ℝ] ComplexVector n)
    (V : Fin r → ComplexVector n) (s : Fin r) :
    (fun j => Function.update J s (K s) j (V j))=
      Function.update (fun j => J j (V j)) s (K s (V s)) := by
  funext j
  by_cases hjs : j=s
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hjs]

theorem tensorForm_pullback_fderiv
    (F : ComplexVector n → RealTensorForm n r) (f : ComplexVector n → ComplexVector n)
    (z u : ComplexVector n) (V : Fin r → ComplexVector n)
    (hF : DifferentiableAt ℝ F (f z)) (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fun w => (F (f w)).compContinuousLinearMap
      (fun _ : Fin r => fderiv ℝ f w)) z u V =
      (fderiv ℝ F (f z) (fderiv ℝ f z u)) (fun j => fderiv ℝ f z (V j))+
        ∑ s : Fin r, F (f z) (Function.update (fun j => fderiv ℝ f z (V j)) s
          (fderiv ℝ (fderiv ℝ f) z u (V s))) := by
  have hfD := hf.differentiableAt (by norm_num)
  have hJ := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomp : DifferentiableAt ℝ (fun w => F (f w)) z := hF.comp z hfD
  have hd := fderiv_continuousMultilinearMapCompContinuousLinearMap
    (f := fun w => F (f w)) (g := fun (_ : Fin r) w => fderiv ℝ f w)
    hcomp (fun _ => hJ)
  have he := congrArg (fun L : ComplexVector n →L[ℝ] RealTensorForm n r => L u V) hd
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply,
    ContinuousLinearMap.pi_apply] at he
  have hcompD : fderiv ℝ (fun w => F (f w)) z=
      (fderiv ℝ F (f z)).comp (fderiv ℝ f z) := by
    simpa only [Function.comp_def] using fderiv_comp z hF hfD
  rw [hcompD] at he
  have hmaps (s : Fin r) :
      (fun j => Function.update (fun _ : Fin r => fderiv ℝ f z) s
        (fderiv ℝ (fun w => fderiv ℝ f w) z u) j (V j))=
      Function.update (fun j => fderiv ℝ f z (V j)) s
        (fderiv ℝ (fderiv ℝ f) z u (V s)) :=
    apply_update_linearMaps (fun _ => fderiv ℝ f z)
      (fun _ => fderiv ℝ (fderiv ℝ f) z u) V s
  simpa only [ContinuousLinearMap.comp_apply,hmaps] using he

variable {M : ComplexManifold n}

theorem covariantD_pullback_eval_at
    (h : HermitianField M) (c d : M.Carrier)
    (A B : ComplexVector n → CovTensor n r) (f : ComplexVector n → ComplexVector n)
    (z : ComplexVector n) (hf : ContDiffAt ℝ 2 f z)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) (f z))
    (heq : (fun w => tensorEvalCLM (A w)) =ᶠ[𝓝 z]
      (fun w => (tensorEvalCLM (B (f w))).compContinuousLinearMap
        (fun _ : Fin r => fderiv ℝ f w)))
    (hΓ : ∀ u v : ComplexVector n,
      fderiv ℝ f z (L12Aux.chartChristoffelBilin h c z u v)=
        fderiv ℝ (fderiv ℝ f) z u v+
          L12Aux.chartChristoffelBilin h d (f z) (fderiv ℝ f z u) (fderiv ℝ f z v))
    (u : ComplexVector n) (V : Fin r → ComplexVector n) :
    tensorEvalCLM (covariantD h c A z) (Fin.cons u V)=
      tensorEvalCLM (covariantD h d B (f z))
        (Fin.cons (fderiv ℝ f z u) (fun j => fderiv ℝ f z (V j))) := by
  have hBform : DifferentiableAt ℝ (fun w => tensorEvalCLM (B w)) (f z) :=
    tensorEvalCLMMap.differentiableAt.comp (f z) (differentiableAt_pi.mpr hB)
  have hd := congrArg (fun L : ComplexVector n →L[ℝ] RealTensorForm n r => L u V) heq.fderiv_eq
  rw [tensorForm_pullback_fderiv (fun w => tensorEvalCLM (B w)) f z u V hBform hf] at hd
  have hVal : tensorEvalCLM (A z)=(tensorEvalCLM (B (f z))).compContinuousLinearMap
      (fun _ : Fin r => fderiv ℝ f z) := heq.self_of_nhds
  have hConnection :
      tensorConnectionForm (L12Aux.chartChristoffelBilin h c z) (tensorEvalCLM (A z)) u V =
      (∑ s : Fin r, tensorEvalCLM (B (f z))
        (Function.update (fun j => fderiv ℝ f z (V j)) s (fderiv ℝ (fderiv ℝ f) z u (V s))))+
      tensorConnectionForm (L12Aux.chartChristoffelBilin h d (f z)) (tensorEvalCLM (B (f z)))
        (fderiv ℝ f z u) (fun j => fderiv ℝ f z (V j)) := by
    rw [tensorConnectionForm_apply,tensorConnectionForm_apply,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [hVal,ContinuousMultilinearMap.compContinuousLinearMap_apply,
      linearMap_map_update,hΓ u (V s)]
    exact ((tensorEvalCLM (B (f z))).toContinuousLinearMap
      (fun j => fderiv ℝ f z (V j)) s).map_add _ _
  have hc := congrArg (fun T : RealTensorForm n r => T V)
    (tensorEvalCLM_covariantD h c A z u hA)
  change tensorEvalCLM (covariantD h c A z) (Fin.cons u V)=
    (fderiv ℝ (fun w => tensorEvalCLM (A w)) z u) V-
      tensorConnectionForm (L12Aux.chartChristoffelBilin h c z) (tensorEvalCLM (A z)) u V at hc
  rw [hConnection] at hc
  have hb := congrArg (fun T : RealTensorForm n r => T (fun j => fderiv ℝ f z (V j)))
    (tensorEvalCLM_covariantD h d B (f z) (fderiv ℝ f z u) hB)
  change tensorEvalCLM (covariantD h d B (f z))
      (Fin.cons (fderiv ℝ f z u) (fun j => fderiv ℝ f z (V j))) =
    (fderiv ℝ (fun w => tensorEvalCLM (B w)) (f z) (fderiv ℝ f z u))
      (fun j => fderiv ℝ f z (V j))-
      tensorConnectionForm (L12Aux.chartChristoffelBilin h d (f z)) (tensorEvalCLM (B (f z)))
        (fderiv ℝ f z u) (fun j => fderiv ℝ f z (V j)) at hb
  linarith [hc,hb,hd]

theorem covariantD_pullback_at
    (h : HermitianField M) (c d : M.Carrier)
    (A B : ComplexVector n → CovTensor n r) (f : ComplexVector n → ComplexVector n)
    (z : ComplexVector n) (hf : ContDiffAt ℝ 2 f z)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) (f z))
    (heq : (fun w => tensorEvalCLM (A w)) =ᶠ[𝓝 z]
      (fun w => (tensorEvalCLM (B (f w))).compContinuousLinearMap
        (fun _ : Fin r => fderiv ℝ f w)))
    (hΓ : ∀ u v : ComplexVector n,
      fderiv ℝ f z (L12Aux.chartChristoffelBilin h c z u v)=
        fderiv ℝ (fderiv ℝ f) z u v+
          L12Aux.chartChristoffelBilin h d (f z) (fderiv ℝ f z u) (fderiv ℝ f z v)) :
    tensorEvalCLM (covariantD h c A z)=
      (tensorEvalCLM (covariantD h d B (f z))).compContinuousLinearMap
        (fun _ : Fin (r+1) => fderiv ℝ f z) := by
  ext V
  have hh := covariantD_pullback_eval_at h c d A B f z hf hA hB heq hΓ (V 0) (Fin.tail V)
  have hvec : Fin.cons (fderiv ℝ f z (V 0)) (fun j => fderiv ℝ f z (Fin.tail V j))=
      (fun j : Fin (r+1) => fderiv ℝ f z (V j)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  rw [hvec] at hh
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,Fin.cons_self_tail] using hh

end Yau.LeafProofs.L23Aux
