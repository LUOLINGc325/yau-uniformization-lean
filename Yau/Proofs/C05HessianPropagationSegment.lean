import Yau.Proofs.C05HessianPropagationDerivative
import Yau.Proofs.C05HessianPropagationNorm
import Yau.LeafProofs.L12HopfRinow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The Hessian difference on the same actual minimizing geodesic. -/
noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C05HessianPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

 theorem parallelHessian_zero (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj) :
    parallelHessian g f p w 0 = phaseHessian g.form f ⟨p.proj,w⟩ := by
  rw [parallelHessian,realParallelLift_zero]

 theorem parallelField_realNormSq (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj) (t : ℝ) :
    realNormSq g.form (realGeodesicFlow g p t).proj
      (realTangentEquiv _ (realParallelField g p w t)) =
        realTangentEnergy g.form (⟨p.proj,w⟩ : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) := by
  change realTangentEnergy g.form
    (⟨(realGeodesicFlow g p t).proj,realParallelField g p w t⟩ :
      TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) = _
  rw [realParallelField_totalSpace]
  exact realParallelLift_energy g p w t

 theorem geodesic_velocity_realNorm (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (t : ℝ) :
    realNorm g.form (realGeodesicFlow g p t).proj
      (realTangentEquiv _ (realGeodesicFlow g p t).2) =
        Real.sqrt (realTangentEnergy g.form p) := by
  change Real.sqrt (realTangentEnergy g.form (realGeodesicFlow g p t)) = _
  rw [realGeodesicFlow_energy]

 theorem parallelHessian_difference_le (g : SmoothMetric M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) {C : ℝ} (hC : 0 ≤ C) (U : Set M.Carrier)
    (hthird : ∀ x ∈ U, scalarJetNorm g.form f 3 x ≤ C)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj)
    (hU : ∀ t ∈ Set.Icc (0:ℝ) 1, (realGeodesicFlow g p t).proj ∈ U) :
    |parallelHessian g f p w 1 - phaseHessian g.form f ⟨p.proj,w⟩| ≤
      C * Real.sqrt (realTangentEnergy g.form p) *
        realTangentEnergy g.form (⟨p.proj,w⟩ : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) := by
  let q := parallelHessian g f p w
  let B := C * Real.sqrt (realTangentEnergy g.form p) *
    realTangentEnergy g.form (⟨p.proj,w⟩ : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
  have hq (t : ℝ) := parallelHessian_hasDerivAt g f hf p w t
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : |deriv q t| ≤ B := by
    rw [(hq t).deriv]
    have H := scalarJet_three_evaluation_le g.form f (realGeodesicFlow g p t).proj
      (realTangentEquiv _ (realGeodesicFlow g p t).2)
      (realTangentEquiv _ (realParallelField g p w t)) hC (hthird _ (hU t ht))
    rw [parallelField_realNormSq,geodesic_velocity_realNorm] at H
    simpa only [tangent_coordinates_real_equiv] using H
  have hcont : ContinuousOn q (Set.Icc (0:ℝ) 1) :=
    fun t _ => (hq t).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ q (interior (Set.Icc (0:ℝ) 1)) :=
    fun t _ => (hq t).differentiableAt.differentiableWithinAt
  have hu := (convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun t ht => (le_abs_self _).trans (hbound t (interior_subset ht)))
    0 (by simp) 1 (by simp) zero_le_one
  have hn := (convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le hcont.neg hdiff.neg
    (show ∀ t ∈ interior (Set.Icc (0:ℝ) 1), deriv (fun s => -q s) t ≤ B by
      intro t ht
      rw [deriv.fun_neg]
      have H := (abs_le.mp (hbound t (interior_subset ht))).1
      linarith)
    0 (by simp) 1 (by simp) zero_le_one
  have H : |q 1-q 0| ≤ B := by
    apply abs_le.mpr
    constructor <;> simp only [sub_zero,mul_one,Pi.neg_apply] at hu hn <;> linarith
  simpa only [q,parallelHessian_zero] using H

 theorem phaseHessian_center_vector (k : HermitianField M) (f : M.Carrier → ℝ)
    (q : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (o : M.Carrier) (hq : q.proj = o) :
    ∃ w : TangentVector M o, realNormSq k o w = realTangentEnergy k q ∧
      realHess k f o w w = phaseHessian k f q := by
  rcases q with ⟨x,v⟩
  dsimp only at hq
  subst o
  exact ⟨realTangentEquiv x v,rfl,rfl⟩

 theorem exists_center_vector_hessian_difference_le
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (hf : SmoothFn f) (o : M.Carrier)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hthird : ∀ x ∈ distBall g.form o R, scalarJetNorm g.form f 3 x ≤ C)
    (x : M.Carrier) (hx : x ∈ distBall g.form o R) (v : TangentVector M x) :
    ∃ w : TangentVector M o, realNormSq g.form o w = realNormSq g.form x v ∧
      |realHess g.form f x v v-realHess g.form f o w w| ≤
        C * inducedDistance g.form o x * realNormSq g.form x v := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  obtain ⟨u,hu,hn⟩ := exists_minimizing_realExponential g x o
  rw [g.induced_distance_symm x o] at hn
  let p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier := ⟨x,u⟩
  let v₀ := (realTangentEquiv x).symm v
  have hend : (realGeodesicFlow g p 1).proj = o := hu
  have hU (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : (realGeodesicFlow g p t).proj ∈ distBall g.form o R := by
    apply (mem_distBall_iff g o _ hR).mpr
    have H := realGeodesicFlow_base_dist_le g p 1 t
    rw [hend,abs_of_nonpos (sub_nonpos.mpr ht.2)] at H
    have hL0 := g.induced_distance_nonneg o x
    have hL := (mem_distBall_iff g o x hR).mp hx
    change inducedDistance g.form o (realGeodesicFlow g p t).proj ≤ ‖u‖ * -(t-1) at H
    rw [hn] at H
    nlinarith [ht.1,ht.2]
  have H := parallelHessian_difference_le g f hf hC (distBall g.form o R) hthird p v₀ hU
  have hEnergy : realTangentEnergy g.form
      (⟨p.proj,v₀⟩ : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) = realNormSq g.form x v := by
    change realNormSq g.form x (realTangentEquiv x ((realTangentEquiv x).symm v)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hInitial : phaseHessian g.form f ⟨p.proj,v₀⟩ = realHess g.form f x v v := by
    simp only [phaseHessian,p,v₀,ContinuousLinearEquiv.apply_symm_apply]
  have hSpeed : Real.sqrt (realTangentEnergy g.form p) = inducedDistance g.form o x := by
    rw [realTangentEnergy_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
    exact hn
  obtain ⟨w,hwN,hwH⟩ := phaseHessian_center_vector g.form f (realParallelLift g p v₀ 1) o
    ((realParallelLift_proj g p v₀ 1).trans hend)
  have hParallelN := realParallelLift_energy g p v₀ 1
  rw [hEnergy] at hParallelN
  refine ⟨w,hwN.trans hParallelN,?_⟩
  rw [hSpeed,hEnergy,hInitial] at H
  change |phaseHessian g.form f (realParallelLift g p v₀ 1)-realHess g.form f x v v| ≤ _ at H
  rw [← hwH] at H
  simpa only [abs_sub_comm] using H

end Yau.Proofs.C05HessianPropagationAux
