import Yau.LeafProofs.L23TensorSlots

/-! The commutator of the original covariant derivative in arbitrary rank. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux L19Aux

variable {n : ℕ} {M : ComplexManifold n} {r : ℕ}

theorem covariantD_cons (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (i : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c A z (Fin.cons i v) = rDeriv (fun w => A w v) z i -
      tensorConnectionAction (L12Aux.connectionMatrix h c z i) (A z) v := by
  simp only [covariantD,Fin.cons_zero,Fin.cons_succ,
    tensorConnectionAction,tensorSlotAction,L12Aux.connectionMatrix]

theorem covariantD_twice_cons_split (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v)) =
      covariantD h c (fun w v => covariantD h c A w (Fin.cons j v)) z (Fin.cons i v)-
        ∑ b, christoffel h c z b i j*covariantD h c A z (Fin.cons b v) := by
  rw [covariantD_cons,covariantD_cons]
  simp only [tensorConnectionAction,tensorSlotAction,L12Aux.connectionMatrix,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.update_cons_zero,←Fin.cons_update]
  ring

theorem rDeriv_covariantD_cons (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    rDeriv (fun w => covariantD h c A w (Fin.cons j v)) z i =
      rDeriv (fun w => rDeriv (fun u => A u v) w j) z i -
        tensorConnectionAction (L12Aux.connectionDerivativeMatrix h c z i j) (A z) v -
        tensorConnectionAction (L12Aux.connectionMatrix h c z j)
          (fun v => rDeriv (fun w => A w v) z i) v := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hprod (s : Fin r) (b : RIdx n) :=
    (christoffel_contDiffOn h hh c b j (v s)).mul (hA (Function.update v s b))
  have hinner (s : Fin r) : ContDiffOn ℝ ∞
      (fun w => ∑ b, christoffel h c w b j (v s)*A w (Function.update v s b))
      (chartTarget c) := ContDiffOn.sum (fun b _ => hprod s b)
  have hsum : ContDiffOn ℝ ∞ (fun w => ∑ s : Fin r, ∑ b,
      christoffel h c w b j (v s)*A w (Function.update v s b)) (chartTarget c) :=
    ContDiffOn.sum (fun s _ => hinner s)
  simp only [covariantD_cons,tensorConnectionAction,tensorSlotAction,L12Aux.connectionMatrix]
  rw [rDeriv_sub
    (((L12Aux.rDeriv_contDiffOn hO (hA v) j).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
    ((hsum.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)),
    rDeriv_sum _ (fun s => ((hinner s).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))]
  have hdiffΓ (b : RIdx n) (s : Fin r) :=
    ((christoffel_contDiffOn h hh c b j (v s)).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdiffA (w : Fin r → RIdx n) :=
    ((hA w).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  simp_rw [rDeriv_sum _ (fun b => ((hprod _ b).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))]
  simp_rw [rDeriv_mul (hdiffΓ _ _) (hdiffA _)]
  simp only [L12Aux.connectionDerivativeMatrix,Finset.sum_add_distrib]
  ring

theorem covariantD_twice_cons (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v)) =
      rDeriv (fun w => rDeriv (fun u => A u v) w j) z i -
        tensorConnectionAction (L12Aux.connectionDerivativeMatrix h c z i j) (A z) v -
        tensorConnectionAction (L12Aux.connectionMatrix h c z j)
          (fun v => rDeriv (fun w => A w v) z i) v -
        (∑ b, christoffel h c z b i j * covariantD h c A z (Fin.cons b v)) -
        tensorConnectionAction (L12Aux.connectionMatrix h c z i)
          (fun v => covariantD h c A z (Fin.cons j v)) v := by
  rw [covariantD_cons,rDeriv_covariantD_cons h hh c A hA hz]
  simp only [tensorConnectionAction,tensorSlotAction,L12Aux.connectionMatrix,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.update_cons_zero,←Fin.cons_update]
  ring

theorem covariantD_commutator (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (i j : RIdx n) (v : Fin r → RIdx n) :
    covariantD h c (covariantD h c A) z (Fin.cons i (Fin.cons j v)) -
      covariantD h c (covariantD h c A) z (Fin.cons j (Fin.cons i v)) =
      -∑ s : Fin r, ∑ b : RIdx n,
        riemannCoeff h c z i j (v s) b*A z (Function.update v s b) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hA2 : ContDiffAt ℝ 2 (fun w => A w v) z :=
    ((hA v).contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  have hsecond : rDeriv (fun w => rDeriv (fun u => A u v) w j) z i =
      rDeriv (fun w => rDeriv (fun u => A u v) w i) z j := by
    rw [rDeriv_rDeriv_eq_hessian hA2,rDeriv_rDeriv_eq_hessian hA2]
    exact hA2.isSymmSndFDerivAt (by norm_num) (realVec i) (realVec j)
  have htorsion : (∑ b, christoffel h c z b i j*covariantD h c A z (Fin.cons b v)) =
      ∑ b, christoffel h c z b j i*covariantD h c A z (Fin.cons b v) := by
    simp only [L12Aux.christoffel_symm_lower h c z (a := i) (b := j)]
  rw [covariantD_twice_cons h hh c A hA hz,covariantD_twice_cons h hh c A hA hz,
    hsecond,htorsion]
  simp_rw [covariantD_cons,tensorConnectionAction_sub_tensor]
  have hcomm := tensorConnectionAction_commutator
    (L12Aux.connectionMatrix h c z i) (L12Aux.connectionMatrix h c z j) (A z) v
  have hcurv : (∑ s : Fin r, ∑ b : RIdx n,
      riemannCoeff h c z i j (v s) b*A z (Function.update v s b)) =
      tensorConnectionAction (L12Aux.curvatureMatrix h c z i j) (A z) v := rfl
  rw [hcurv,L12Aux.curvatureMatrix_eq,
    tensorConnectionAction_sub_matrix,tensorConnectionAction_add_matrix,
    tensorConnectionAction_sub_matrix]
  rw [tensorConnectionAction_sub_matrix] at hcomm
  linarith

end Yau.LeafProofs.L23Aux
