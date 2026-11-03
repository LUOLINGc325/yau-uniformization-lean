import Yau.LeafProofs.L23CovariantPermutation
import Yau.LeafProofs.L23CovariantBianchi

/-! The curvature symmetries also hold after actual covariant
differentiation, by equalities on open chart neighborhoods. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def curvaturePairSlots : Equiv.Perm (Fin 4) where
  toFun s := ![2,3,0,1] s
  invFun s := ![2,3,0,1] s
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by fin_cases s <;> rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem rmTensor_swap_first (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (i j k l : RIdx n) : rmTensor h c z ![i,j,k,l]=-rmTensor h c z ![j,i,k,l] := by
  change (∑ p, realMetricFn h c z p l*riemannCoeff h c z i j k p)=
    -(∑ p, realMetricFn h c z p l*riemannCoeff h c z j i k p)
  simp only [L12Aux.riemannCoeff_swap h c z i j k, mul_neg,Finset.sum_neg_distrib]

theorem rmTensor_swap_last (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    rmTensor h c z ![i,j,k,l]=-rmTensor h c z ![i,j,l,k] :=
  curvature4_swap_last h hh c z hz i j k l

theorem rmTensor_pair_swap (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    rmTensor h c z ![i,j,k,l]=rmTensor h c z ![k,l,i,j] :=
  curvature4_pair_swap h hh c z hz i j k l

theorem covariantD_rmTensor_swap_first (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j k l : RIdx n) :
    covariantD h c (rmTensor h c) z ![a,i,j,k,l]=
      -covariantD h c (rmTensor h c) z ![a,j,i,k,l] := by
  let e := Equiv.swap (0 : Fin 4) 1
  have hs : (fun w v => rmTensor h c w (v ∘ e))=ᶠ[𝓝 z]
      (fun w v => (-1 : ℝ)*rmTensor h c w v) := by
    filter_upwards [] with w
    funext v
    have hv : v=![v 0,v 1,v 2,v 3] := by funext s; fin_cases s <;> rfl
    have hp : v ∘ e=![v 1,v 0,v 2,v 3] := by
      funext s
      fin_cases s <;> simp [e,Equiv.swap_apply_def]
    rw [hp,rmTensor_swap_first h c w (v 1) (v 0) (v 2) (v 3)]
    rw [←hv]
    ring
  have hA (v : Fin 4 → RIdx n) := ((rmTensor_contDiffOn h hh c v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hd := covariantD_signedPermutation_at h c (rmTensor h c) e z (-1) hA hs a ![i,j,k,l]
  have hp : ![i,j,k,l] ∘ e=![j,i,k,l] := by
    funext s
    fin_cases s <;> simp [e,Equiv.swap_apply_def]
  rw [hp] at hd
  change covariantD h c (rmTensor h c) z ![a,j,i,k,l]=
    (-1)*covariantD h c (rmTensor h c) z ![a,i,j,k,l] at hd
  linarith

theorem covariantD_rmTensor_swap_last (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j k l : RIdx n) :
    covariantD h c (rmTensor h c) z ![a,i,j,k,l]=
      -covariantD h c (rmTensor h c) z ![a,i,j,l,k] := by
  let e := Equiv.swap (2 : Fin 4) 3
  have hs : (fun w v => rmTensor h c w (v ∘ e))=ᶠ[𝓝 z]
      (fun w v => (-1 : ℝ)*rmTensor h c w v) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    funext v
    have hv : v=![v 0,v 1,v 2,v 3] := by funext s; fin_cases s <;> rfl
    have hp : v ∘ e=![v 0,v 1,v 3,v 2] := by
      funext s
      fin_cases s <;> simp [e,Equiv.swap_apply_def]
    rw [hp,rmTensor_swap_last h hh c hw (v 0) (v 1) (v 3) (v 2),←hv]
    ring
  have hA (v : Fin 4 → RIdx n) := ((rmTensor_contDiffOn h hh c v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hd := covariantD_signedPermutation_at h c (rmTensor h c) e z (-1) hA hs a ![i,j,k,l]
  have hp : ![i,j,k,l] ∘ e=![i,j,l,k] := by
    funext s
    fin_cases s <;> simp [e,Equiv.swap_apply_def]
  rw [hp] at hd
  change covariantD h c (rmTensor h c) z ![a,i,j,l,k]=
    (-1)*covariantD h c (rmTensor h c) z ![a,i,j,k,l] at hd
  linarith

theorem covariantD_rmTensor_pair_swap (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j k l : RIdx n) :
    covariantD h c (rmTensor h c) z ![a,i,j,k,l]=
      covariantD h c (rmTensor h c) z ![a,k,l,i,j] := by
  have hs : (fun w v => rmTensor h c w (v ∘ curvaturePairSlots))=ᶠ[𝓝 z]
      (fun w v => (1 : ℝ)*rmTensor h c w v) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    funext v
    have hv : v=![v 0,v 1,v 2,v 3] := by funext s; fin_cases s <;> rfl
    have hp : v ∘ curvaturePairSlots=![v 2,v 3,v 0,v 1] := by
      funext s
      fin_cases s <;> rfl
    rw [hp,rmTensor_pair_swap h hh c hw (v 2) (v 3) (v 0) (v 1),←hv,one_mul]
  have hA (v : Fin 4 → RIdx n) := ((rmTensor_contDiffOn h hh c v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hd := covariantD_signedPermutation_at h c (rmTensor h c) curvaturePairSlots z 1 hA hs a ![i,j,k,l]
  have hp : ![i,j,k,l] ∘ curvaturePairSlots=![k,l,i,j] := by
    funext s
    fin_cases s <;> rfl
  rw [hp,one_mul] at hd
  exact hd.symm

end Yau.LeafProofs.L23Aux
