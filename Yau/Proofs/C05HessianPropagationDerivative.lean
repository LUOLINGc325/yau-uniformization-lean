import Yau.Proofs.C05HessianPropagationJets
import Yau.LeafProofs.L12ParallelTransport

/-! Differentiating the actual Hessian on a genuinely parallel vector. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C05HessianPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def tensorTwoBilinMap (A : CovTensor n 2) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ :=
  ∑ a : RIdx n, ∑ b : RIdx n,
    A ![a,b] • ((realCoordCLM a).smulRight (realCoordCLM b))

 theorem tensorTwoBilinMap_apply (A : CovTensor n 2) (u v : ComplexVector n) :
    tensorTwoBilinMap A u v = tensorEvalCLM A ![u,v] := by
  simp [tensorTwoBilinMap,tensorEvalCLM_two,realCoordCLM_apply,mul_assoc]

 theorem chart_hessian_parallel_hasDerivAt (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c : M.Carrier)
    (z V : ℝ → ComplexVector n) (t : ℝ) (T : ComplexVector n)
    (hz : z t ∈ chartTarget c) (hZ : HasDerivAt z T t)
    (hV : HasDerivAt V (-chartChristoffelBilin k c (z t) T (V t)) t) :
    HasDerivAt (fun s => tensorEvalCLM (scalarJet k f c 2 (z s)) ![V s,V s])
      (tensorEvalCLM (scalarJet k f c 3 (z t)) ![T,V t,V t]) t := by
  let A := scalarJet k f c 2 (z t)
  let A' : CovTensor n 2 := fun v => fderiv ℝ (fun w => scalarJet k f c 2 w v) (z t) T
  let Γ := chartChristoffelBilin k c (z t)
  have hcoeff (v : Fin 2 → RIdx n) : DifferentiableAt ℝ (fun w => scalarJet k f c 2 w v) (z t) :=
    ((scalarJet_contDiffOn k hk f hf c 2 v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hBsum := HasDerivAt.sum (fun (a : RIdx n) (_ : a ∈ Finset.univ) =>
    HasDerivAt.sum (fun (b : RIdx n) (_ : b ∈ Finset.univ) =>
      (((hcoeff ![a,b]).hasFDerivAt.comp_hasDerivAt t hZ).mul
        ((realCoordCLM a).hasFDerivAt.comp_hasDerivAt t hV)).mul
          ((realCoordCLM b).hasFDerivAt.comp_hasDerivAt t hV)))
  have hsum_apply (B : CovTensor n 2) (u v : ComplexVector n) :
      tensorTwoBilinMap B u v =
        ∑ a : RIdx n, ∑ b : RIdx n, B ![a,b]*realCoord u a*realCoord v b := by
    rw [tensorTwoBilinMap_apply,tensorEvalCLM_two]
  have hprod : HasDerivAt
      (fun s => tensorTwoBilinMap (scalarJet k f c 2 (z s)) (V s) (V s))
      (tensorTwoBilinMap A' (V t) (V t) +
        tensorTwoBilinMap A (-Γ T (V t)) (V t) +
          tensorTwoBilinMap A (V t) (-Γ T (V t))) t := by
    convert hBsum using 1
    · funext s
      simp only [hsum_apply,Finset.sum_apply,Pi.mul_apply,Function.comp_apply,realCoordCLM_apply]
    · simp only [hsum_apply,Pi.mul_apply,Function.comp_apply,realCoordCLM_apply]
      simp_rw [add_mul,Finset.sum_add_distrib]
      rfl
  have hcov := tensorEvalCLM_covariantD k c (scalarJet k f c 2) (z t) T hcoeff
  have he := congrArg (fun B : RealTensorForm n 2 => B ![V t,V t]) hcov
  have hder : (fderiv ℝ (fun w => tensorEvalCLM (scalarJet k f c 2 w)) (z t) T) ![V t,V t] =
      tensorTwoBilinMap A' (V t) (V t) := by
    rw [tensorEvalCLM_fderiv _ hcoeff]
    exact (tensorTwoBilinMap_apply A' (V t) (V t)).symm
  have hup0 : Function.update ![V t,V t] 0 (Γ T (V t)) = ![Γ T (V t),V t] := by
    funext i
    fin_cases i <;> simp
  have hup1 : Function.update ![V t,V t] 1 (Γ T (V t)) = ![V t,Γ T (V t)] := by
    funext i
    fin_cases i <;> simp
  have hconn : tensorConnectionForm Γ (tensorEvalCLM A) T ![V t,V t] =
      tensorTwoBilinMap A (Γ T (V t)) (V t) + tensorTwoBilinMap A (V t) (Γ T (V t)) := by
    rw [tensorConnectionForm_apply,Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [hup0,hup1]
    simp only [tensorTwoBilinMap_apply]
  change tensorEvalCLM (scalarJet k f c 3 (z t)) ![T,V t,V t] =
    (fderiv ℝ (fun w => tensorEvalCLM (scalarJet k f c 2 w)) (z t) T) ![V t,V t] -
      tensorConnectionForm Γ (tensorEvalCLM A) T ![V t,V t] at he
  rw [hder,hconn] at he
  have hp := hprod.congr_deriv (show
      tensorTwoBilinMap A' (V t) (V t) + tensorTwoBilinMap A (-Γ T (V t)) (V t) +
        tensorTwoBilinMap A (V t) (-Γ T (V t)) =
          tensorEvalCLM (scalarJet k f c 3 (z t)) ![T,V t,V t] by
    rw [he]
    simp only [ContinuousLinearMap.add_apply,map_neg,neg_apply]
    ring)
  exact hp.congr_of_eventuallyEq (Eventually.of_forall (fun s =>
    (tensorTwoBilinMap_apply (scalarJet k f c 2 (z s)) (V s) (V s)).symm))

def phaseHessian (k : HermitianField M) (f : M.Carrier → ℝ)
    (q : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) : ℝ :=
  realHess k f q.proj (realTangentEquiv q.proj q.2) (realTangentEquiv q.proj q.2)

def parallelHessian (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj) (t : ℝ) : ℝ :=
  phaseHessian g.form f (realParallelLift g p w t)

 theorem parallelHessian_eq_field (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj) (t : ℝ) :
    parallelHessian g f p w t = realHess g.form f (realGeodesicFlow g p t).proj
      (realTangentEquiv _ (realParallelField g p w t))
      (realTangentEquiv _ (realParallelField g p w t)) := by
  unfold parallelHessian
  rw [← realParallelField_totalSpace g p w t]
  rfl

 theorem parallelHessian_hasDerivAt (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj) (t : ℝ) :
    let x := (realGeodesicFlow g p t).proj
    HasDerivAt (parallelHessian g f p w)
      (tensorEvalCLM (scalarJet g.form f x 3 (chartPt x x))
        ![realTangentCoords x x (realGeodesicFlow g p t).2,
          realTangentCoords x x (realParallelField g p w t),
          realTangentCoords x x (realParallelField g p w t)]) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let x := (realGeodesicFlow g p t).proj
  have hZ := realGeodesicFlow_baseCoords_hasDerivAt g p t
  have hV := realParallelField_coords_hasDerivAt g p w t
  have H := chart_hessian_parallel_hasDerivAt g.form (metricSmooth_of_smoothMetric g) f hf x
    (fun s => chartPt x (realGeodesicFlow g p s).proj)
    (fun s => realTangentCoords x (realGeodesicFlow g p s).proj (realParallelField g p w s))
    t (realTangentCoords x x (realGeodesicFlow g p t).2) (mem_extChartAt_target x) hZ hV
  have hcont := ((FiberBundle.continuous_proj (ComplexVector n)
    (TangentSpace 𝓘(ℝ,ComplexVector n))).comp (realGeodesicFlow_contMDiff g p).continuous).continuousAt (x := t)
  apply H.congr_of_eventuallyEq
  filter_upwards [hcont.preimage_mem_nhds
    ((chartAt (ComplexVector n) x).open_source.mem_nhds (mem_chart_source _ _))] with s hs
  rw [parallelHessian_eq_field]
  exact realHess_in_fixed_chart g.form (metricSmooth_of_smoothMetric g) f hf x
    (realGeodesicFlow g p s).proj hs (realParallelField g p w s) (realParallelField g p w s)

end Yau.Proofs.C05HessianPropagationAux
