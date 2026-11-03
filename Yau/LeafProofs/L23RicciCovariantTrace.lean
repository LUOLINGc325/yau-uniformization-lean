import Yau.LeafProofs.L23CovariantTrace
import Yau.LeafProofs.L23CovariantPermutation
import Yau.LeafProofs.L23RicciDerivative

/-! The Ricci derivative is the genuine metric trace of the full Rm
derivative, with the original order of all tensor slots. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem covariantD_ricciTensor_trace (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k : RIdx n) :
    covariantD h c (ricciTensor h c) z ![i,j,k]=
      ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        covariantD h c (rmTensor h c) z ![i,a,j,k,b] := by
  let A : ComplexVector n → CovTensor n 4 := fun w v => rmTensor h c w (v ∘ ricciTraceSlots)
  have hA (v : Fin 4 → RIdx n) := ((rmTensor_contDiffOn h hh c (v ∘ ricciTraceSlots)).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hd := covariantD_tensorMetricTrace h hh c A hz hA i ![j,k]
  have hfield : (fun w => tensorMetricTrace (realMetricFn h c w)⁻¹ (A w))=
      ricciTensor h c := by
    funext w v
    exact (realRicciCoeff_eq_tensorMetricTrace h c w v).symm
  rw [hfield] at hd
  change covariantD h c (ricciTensor h c) z ![i,j,k]=_ at hd
  rw [hd]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change covariantD h c (fun w v => rmTensor h c w (v ∘ ricciTraceSlots)) z
    (Fin.cons i (Fin.cons a (Fin.cons b ![j,k])))=_
  rw [covariantD_permute_cons]
  have hv : (Fin.cons a (Fin.cons b ![j,k])) ∘ ricciTraceSlots=![a,j,k,b] := by
    funext s
    fin_cases s <;> rfl
  rw [hv]
  rfl

theorem covariantD_ricciTensor_symm (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k : RIdx n) :
    covariantD h c (ricciTensor h c) z ![i,j,k]=
      covariantD h c (ricciTensor h c) z ![i,k,j] := by
  rw [covariantD_ricciTensor_three,covariantD_ricciTensor_three]
  have heq : (fun w => realRicciCoeff h c w j k)=ᶠ[𝓝 z]
      (fun w => realRicciCoeff h c w k j) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    exact realRicciCoeff_symm h hh c hw j k
  have h1 : rDeriv (fun w => realRicciCoeff h c w j k) z i=
      rDeriv (fun w => realRicciCoeff h c w k j) z i := by
    unfold rDeriv
    rw [heq.fderiv_eq]
  have h2 : (∑ p, christoffel h c z p i j*realRicciCoeff h c z p k)=
      ∑ p, christoffel h c z p i j*realRicciCoeff h c z k p := by
    simp only [realRicciCoeff_symm h hh c hz (j := k)]
  have h3 : (∑ p, christoffel h c z p i k*realRicciCoeff h c z j p)=
      ∑ p, christoffel h c z p i k*realRicciCoeff h c z p j := by
    simp only [realRicciCoeff_symm h hh c hz j]
  rw [h1,h2,h3]
  ring

end Yau.LeafProofs.L23Aux
