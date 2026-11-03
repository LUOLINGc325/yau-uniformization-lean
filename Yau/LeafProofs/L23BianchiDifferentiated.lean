import Yau.LeafProofs.L23ContractedBianchi
import Yau.LeafProofs.L23RmSecondRicciTime

/-! Covariant derivatives of Bianchi identities are obtained on actual
open chart neighborhoods, never by differentiating an isolated equality. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def bianchiDerivativeCycle : Equiv.Perm (Fin 5) where
  toFun s := ![2,0,1,3,4] s
  invFun s := ![1,2,0,3,4] s
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by fin_cases s <;> rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem covariantD_twice_rmTensor_bianchi (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b i j k l : RIdx n) :
    covariantD h c (covariantD h c (rmTensor h c)) z ![a,b,i,j,k,l]=
      covariantD h c (covariantD h c (rmTensor h c)) z ![a,i,b,j,k,l]-
        covariantD h c (covariantD h c (rmTensor h c)) z ![a,j,b,i,k,l] := by
  let A := covariantD h c (rmTensor h c)
  let e := Equiv.swap (0 : Fin 5) 1
  let B : ComplexVector n → CovTensor n 5 := fun w v => A w (v ∘ e)
  let C : ComplexVector n → CovTensor n 5 := fun w v => A w (v ∘ bianchiDerivativeCycle)
  have heq : A=ᶠ[𝓝 z] (fun w => B w-C w) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    funext v
    have hv : v=![v 0,v 1,v 2,v 3,v 4] := by funext s; fin_cases s <;> rfl
    have hs : v ∘ e=![v 1,v 0,v 2,v 3,v 4] := by
      funext s
      fin_cases s <;> simp [e,Equiv.swap_apply_def]
    have hc : v ∘ bianchiDerivativeCycle=![v 2,v 0,v 1,v 3,v 4] := by
      funext s
      fin_cases s <;> rfl
    change A w v=A w (v ∘ e)-A w (v ∘ bianchiDerivativeCycle)
    rw [hs,hc,hv]
    have hB := covariantD_rmTensor_secondBianchi h hh c hw (v 0) (v 1) (v 2) (v 3) (v 4)
    have hS := covariantD_rmTensor_swap_first h hh c hw (v 1) (v 2) (v 0) (v 3) (v 4)
    change covariantD h c (rmTensor h c) w ![v 0,v 1,v 2,v 3,v 4]=
      covariantD h c (rmTensor h c) w ![v 1,v 0,v 2,v 3,v 4]-
        covariantD h c (rmTensor h c) w ![v 2,v 0,v 1,v 3,v 4]
    linarith [hB,hS]
  have hAs (v : Fin 5 → RIdx n) := ((covariantD_contDiffOn h hh c (rmTensor h c)
    (rmTensor_contDiffOn h hh c) v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hBs (v : Fin 5 → RIdx n) : DifferentiableAt ℝ (fun w => B w v) z := hAs (v ∘ e)
  have hCs (v : Fin 5 → RIdx n) : DifferentiableAt ℝ (fun w => C w v) z := hAs (v ∘ bianchiDerivativeCycle)
  have hD := covariantD_eventuallyEq h c _ _ z heq
  rw [covariantD_sub_at h c _ _ z hBs hCs] at hD
  have hp := congrFun hD (Fin.cons a ![b,i,j,k,l])
  change covariantD h c A z (Fin.cons a ![b,i,j,k,l])=
    covariantD h c (fun w v => A w (v ∘ e)) z (Fin.cons a ![b,i,j,k,l])-
      covariantD h c (fun w v => A w (v ∘ bianchiDerivativeCycle)) z
        (Fin.cons a ![b,i,j,k,l]) at hp
  rw [covariantD_permute_cons,covariantD_permute_cons] at hp
  have hs : ![b,i,j,k,l] ∘ e=![i,b,j,k,l] := by
    funext s
    fin_cases s <;> simp [e,Equiv.swap_apply_def]
  have hc : ![b,i,j,k,l] ∘ bianchiDerivativeCycle=![j,b,i,k,l] := by
    funext s
    fin_cases s <;> rfl
  rw [hs,hc] at hp
  exact hp

end Yau.LeafProofs.L23Aux
