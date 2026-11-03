import Yau.Proofs.C05RicciPropagationDerivative
import Yau.Proofs.C05RicciPropagationNorm
import Yau.Proofs.C05HessianPropagationSegment

/-! Physical Ricci variation along the same actual minimizing segment. -/
noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C05RicciPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.Proofs.C05HessianPropagationAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem parallelRicci_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj) :
    parallelRicci g p w 0 = phaseRicci g.form ⟨p.proj,w⟩ := by
  rw [parallelRicci,realParallelLift_zero]

 theorem parallelRicci_difference_le (g : SmoothMetric M)
    {C : ℝ} (hC : 0 ≤ C) (U : Set M.Carrier)
    (hthird : ∀ x ∈ U, realRicciJetNorm g.form 1 x ≤ C)
    (p : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ,ComplexVector n) p.proj)
    (hU : ∀ t ∈ Set.Icc (0:ℝ) 1, (realGeodesicFlow g p t).proj ∈ U) :
    |parallelRicci g p w 1 - phaseRicci g.form ⟨p.proj,w⟩| ≤
      C * Real.sqrt (realTangentEnergy g.form p) *
        realTangentEnergy g.form (⟨p.proj,w⟩ : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) := by
  let q := parallelRicci g p w
  let B := C * Real.sqrt (realTangentEnergy g.form p) *
    realTangentEnergy g.form (⟨p.proj,w⟩ : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier)
  have hq (t : ℝ) := parallelRicci_hasDerivAt g p w t
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : |deriv q t| ≤ B := by
    rw [(hq t).deriv]
    have H := ricciJet_one_evaluation_le g.form (realGeodesicFlow g p t).proj
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
  simpa only [q,parallelRicci_zero] using H

 theorem phaseRicci_center_vector (k : HermitianField M)
    (q : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) (o : M.Carrier) (hq : q.proj = o) :
    ∃ w : TangentVector M o, realNormSq k o w = realTangentEnergy k q ∧
      ricciQuad k o w = phaseRicci k q := by
  rcases q with ⟨x,v⟩
  dsimp only at hq
  subst o
  exact ⟨realTangentEquiv x v,rfl,rfl⟩

 theorem exists_center_vector_ricci_difference_le
    (g : SmoothMetric M) (o : M.Carrier)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hthird : ∀ x ∈ distBall g.form o R, realRicciJetNorm g.form 1 x ≤ C)
    (x : M.Carrier) (hx : x ∈ distBall g.form o R) (v : TangentVector M x) :
    ∃ w : TangentVector M o, realNormSq g.form o w = realNormSq g.form x v ∧
      |ricciQuad g.form x v-ricciQuad g.form o w| ≤
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
  have H := parallelRicci_difference_le g hC (distBall g.form o R) hthird p v₀ hU
  have hEnergy : realTangentEnergy g.form
      (⟨p.proj,v₀⟩ : TangentBundle 𝓘(ℝ,ComplexVector n) M.Carrier) = realNormSq g.form x v := by
    change realNormSq g.form x (realTangentEquiv x ((realTangentEquiv x).symm v)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hInitial : phaseRicci g.form ⟨p.proj,v₀⟩ = ricciQuad g.form x v := by
    simp only [phaseRicci,p,v₀,ContinuousLinearEquiv.apply_symm_apply]
  have hSpeed : Real.sqrt (realTangentEnergy g.form p) = inducedDistance g.form o x := by
    rw [realTangentEnergy_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
    exact hn
  obtain ⟨w,hwN,hwH⟩ := phaseRicci_center_vector g.form (realParallelLift g p v₀ 1) o
    ((realParallelLift_proj g p v₀ 1).trans hend)
  have hParallelN := realParallelLift_energy g p v₀ 1
  rw [hEnergy] at hParallelN
  refine ⟨w,hwN.trans hParallelN,?_⟩
  rw [hSpeed,hEnergy,hInitial] at H
  change |phaseRicci g.form (realParallelLift g p v₀ 1)-ricciQuad g.form x v| ≤ _ at H
  rw [← hwH] at H
  simpa only [abs_sub_comm] using H


end Yau.Proofs.C05RicciPropagationAux
