import Yau.LeafProofs.L23ContractedBianchi
import Yau.LeafProofs.L23RmSecondRicciTime

/-! Differentiating the actual contracted Bianchi identity on an open chart. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem covariantD_rmTensor_divergence_derivative (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
      covariantD h c (covariantD h c (rmTensor h c)) z ![i,a,b,j,k,l])=
      -covariantD h c (covariantD h c (ricciTensor h c)) z ![i,k,j,l]+
        covariantD h c (covariantD h c (ricciTensor h c)) z ![i,l,j,k] := by
  let R := covariantD h c (rmTensor h c)
  let A := covariantD h c (ricciTensor h c)
  let e := Equiv.swap (0 : Fin 3) 1
  let E : ComplexVector n → CovTensor n 3 := fun w v => A w (v ∘ e)
  let F : ComplexVector n → CovTensor n 3 := fun w v => A w (v ∘ ricciConnectionCycle)
  let D : ComplexVector n → CovTensor n 3 := fun w =>
    tensorMetricTrace (realMetricFn h c w)⁻¹ (R w)
  have heq : D=ᶠ[𝓝 z] (fun w => F w-E w) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    funext v
    have hs : v ∘ e=![v 1,v 0,v 2] := by
      funext s
      fin_cases s <;> simp [e,Equiv.swap_apply_def]
    have hc : v ∘ ricciConnectionCycle=![v 2,v 0,v 1] := by
      funext s
      fin_cases s <;> rfl
    change tensorMetricTrace (realMetricFn h c w)⁻¹ (R w) v=
      A w (v ∘ ricciConnectionCycle)-A w (v ∘ e)
    rw [hs,hc]
    have hd := covariantD_rmTensor_divergence h hh c hw (v 0) (v 1) (v 2)
    convert hd using 1
    · apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      have hv : Fin.cons a (Fin.cons b v)=![a,b,v 0,v 1,v 2] := by
        funext s
        fin_cases s <;> rfl
      rw [hv]
    · ring
  have hRs (v : Fin 5 → RIdx n) := ((covariantD_contDiffOn h hh c (rmTensor h c)
    (rmTensor_contDiffOn h hh c) v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hRc (v : Fin 2 → RIdx n) : ContDiffOn ℝ ∞ (fun w => ricciTensor h c w v)
      (chartTarget c) := realRicciCoeff_contDiffOn h hh c (v 0) (v 1)
  have hAs (v : Fin 3 → RIdx n) := ((covariantD_contDiffOn h hh c (ricciTensor h c)
    hRc v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hEs (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => E w v) z := hAs (v ∘ e)
  have hFs (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => F w v) z := hAs (v ∘ ricciConnectionCycle)
  have hD := covariantD_eventuallyEq h c _ _ z heq
  rw [covariantD_sub_at h c _ _ z hFs hEs] at hD
  have hp := congrFun hD (Fin.cons i ![j,k,l])
  change covariantD h c D z (Fin.cons i ![j,k,l])=
    covariantD h c (fun w v => A w (v ∘ ricciConnectionCycle)) z (Fin.cons i ![j,k,l])-
      covariantD h c (fun w v => A w (v ∘ e)) z (Fin.cons i ![j,k,l]) at hp
  rw [covariantD_permute_cons,covariantD_permute_cons] at hp
  have hs : ![j,k,l] ∘ e=![k,j,l] := by
    funext s
    fin_cases s <;> simp [e,Equiv.swap_apply_def]
  have hc : ![j,k,l] ∘ ricciConnectionCycle=![l,j,k] := by
    funext s
    fin_cases s <;> rfl
  rw [hs,hc] at hp
  have ht := covariantD_tensorMetricTrace h hh c R hz hRs i ![j,k,l]
  change covariantD h c D z (Fin.cons i ![j,k,l])=_ at ht
  rw [ht] at hp
  change (∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
    covariantD h c (covariantD h c (rmTensor h c)) z ![i,a,b,j,k,l])=
      covariantD h c (covariantD h c (ricciTensor h c)) z ![i,l,j,k]-
        covariantD h c (covariantD h c (ricciTensor h c)) z ![i,k,j,l] at hp
  linarith [hp]

end Yau.LeafProofs.L23Aux
