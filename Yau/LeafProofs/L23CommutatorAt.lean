import Yau.LeafProofs.L23Commutator

/-! The original arbitrary-rank commutator uses only two jets at the point.
This local version applies to fields defined on chart overlaps. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n} {r : ℕ}

theorem rDeriv_covariantD_cons_at (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ v, ContDiffAt ℝ 2 (fun w => A w v) z)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    rDeriv (fun w => covariantD h c A w (Fin.cons j v)) z i =
      rDeriv (fun w => rDeriv (fun u => A u v) w j) z i-
        tensorConnectionAction (L12Aux.connectionDerivativeMatrix h c z i j) (A z) v-
        tensorConnectionAction (L12Aux.connectionMatrix h c z j)
          (fun v => rDeriv (fun w => A w v) z i) v := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hΓ (b : RIdx n) (s : Fin r) :=
    ((christoffel_contDiffOn h hh c b j (v s)).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hAdiff (w : Fin r → RIdx n) := (hA w).differentiableAt (by norm_num)
  have hprod (s : Fin r) (b : RIdx n) : DifferentiableAt ℝ
      (fun w => christoffel h c w b j (v s)*A w (Function.update v s b)) z :=
    (hΓ b s).mul (hAdiff (Function.update v s b))
  have hinner (s : Fin r) : DifferentiableAt ℝ
      (fun w => ∑ b, christoffel h c w b j (v s)*A w (Function.update v s b)) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun b _ => hprod s b)
  have hsum : DifferentiableAt ℝ (fun w => ∑ s : Fin r, ∑ b,
      christoffel h c w b j (v s)*A w (Function.update v s b)) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun s _ => hinner s)
  have hDA : DifferentiableAt ℝ (fun w => rDeriv (fun u => A u v) w j) z := by
    exact (((hA v).fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := realVec j))).differentiableAt one_ne_zero
  simp only [covariantD_cons,tensorConnectionAction,tensorSlotAction,L12Aux.connectionMatrix]
  rw [rDeriv_sub hDA hsum,rDeriv_sum _ hinner]
  simp_rw [rDeriv_sum _ (hprod _),rDeriv_mul (hΓ _ _) (hAdiff _)]
  simp only [L12Aux.connectionDerivativeMatrix,Finset.sum_add_distrib]
  ring

theorem covariantD_twice_cons_at (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ v, ContDiffAt ℝ 2 (fun w => A w v) z)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v)) =
      rDeriv (fun w => rDeriv (fun u => A u v) w j) z i-
        tensorConnectionAction (L12Aux.connectionDerivativeMatrix h c z i j) (A z) v-
        tensorConnectionAction (L12Aux.connectionMatrix h c z j)
          (fun v => rDeriv (fun w => A w v) z i) v-
        (∑ b, christoffel h c z b i j*covariantD h c A z (Fin.cons b v))-
        tensorConnectionAction (L12Aux.connectionMatrix h c z i)
          (fun v => covariantD h c A z (Fin.cons j v)) v := by
  rw [covariantD_cons,rDeriv_covariantD_cons_at h hh c A hz hA]
  simp only [tensorConnectionAction,tensorSlotAction,L12Aux.connectionMatrix,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.update_cons_zero,←Fin.cons_update]
  ring

theorem covariantD_commutator_at (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hA : ∀ v, ContDiffAt ℝ 2 (fun w => A w v) z)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v))-
      covariantD h c (covariantD h c A) z (Fin.cons j (Fin.cons i v)) =
      -∑ s : Fin r, ∑ b : RIdx n,
        riemannCoeff h c z i j (v s) b*A z (Function.update v s b) := by
  have hsecond : rDeriv (fun w => rDeriv (fun u => A u v) w j) z i =
      rDeriv (fun w => rDeriv (fun u => A u v) w i) z j := by
    rw [rDeriv_rDeriv_eq_hessian (hA v),rDeriv_rDeriv_eq_hessian (hA v)]
    exact (hA v).isSymmSndFDerivAt (by norm_num) (realVec i) (realVec j)
  have htorsion : (∑ b, christoffel h c z b i j*covariantD h c A z (Fin.cons b v)) =
      ∑ b, christoffel h c z b j i*covariantD h c A z (Fin.cons b v) := by
    simp only [L12Aux.christoffel_symm_lower h c z (a := i) (b := j)]
  rw [covariantD_twice_cons_at h hh c A hz hA,covariantD_twice_cons_at h hh c A hz hA,
    hsecond,htorsion]
  simp_rw [covariantD_cons,tensorConnectionAction_sub_tensor]
  have hcomm := tensorConnectionAction_commutator
    (L12Aux.connectionMatrix h c z i) (L12Aux.connectionMatrix h c z j) (A z) v
  have hcurv : (∑ s : Fin r, ∑ b : RIdx n,
      riemannCoeff h c z i j (v s) b*A z (Function.update v s b)) =
      tensorConnectionAction (L12Aux.curvatureMatrix h c z i j) (A z) v := rfl
  rw [hcurv,L12Aux.curvatureMatrix_eq,tensorConnectionAction_sub_matrix,
    tensorConnectionAction_add_matrix,tensorConnectionAction_sub_matrix]
  rw [tensorConnectionAction_sub_matrix] at hcomm
  linarith

end Yau.LeafProofs.L23Aux
