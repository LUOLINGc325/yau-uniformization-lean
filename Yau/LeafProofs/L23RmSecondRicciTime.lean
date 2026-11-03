import Yau.LeafProofs.L23RmTimeVariation
import Yau.LeafProofs.L23CovariantPermutation

/-! The exact six second-Ricci-derivative terms in the actual curvature
time variation, before the Bianchi identities eliminate them. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def ricciConnectionCycle : Equiv.Perm (Fin 3) where
  toFun s := ![2,0,1] s
  invFun s := ![1,2,0] s
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by fin_cases s <;> rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem localRealRicciFlow_covariantD_lowerConnectionTensor
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j k l : RIdx n) :
    covariantD (h t) c (lowerConnectionTensor (h t) c
      (fun w => dotChristoffel h c w t)) z ![i,j,k,l]=
      -(σ/2)*(covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,j,k,l]+
        covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,k,j,l]-
          covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,l,j,k]) := by
  let A := covariantD (h t) c (ricciTensor (h t) c)
  let e := Equiv.swap (0 : Fin 3) 1
  let B : ComplexVector n → CovTensor n 3 := fun w v => A w (v ∘ e)
  let C : ComplexVector n → CovTensor n 3 := fun w v => A w (v ∘ ricciConnectionCycle)
  have heq : lowerConnectionTensor (h t) c (fun w => dotChristoffel h c w t)=ᶠ[𝓝 z]
      (fun w v => -(σ/2)*(A w v+B w v-C w v)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz,
      (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds (hO.mem_nhds hx)] with w hw hwo
    rw [localRealRicciFlow_lowerConnectionTensor_eq h O a b σ hO hflow c hw hwo t ht]
    funext v
    have hv : ![v 0,v 1,v 2]=v := by funext s; fin_cases s <;> rfl
    have hs : ![v 1,v 0,v 2]=v ∘ e := by
      funext s
      fin_cases s <;> simp [e,Equiv.swap_apply_def]
    have hc : ![v 2,v 0,v 1]=v ∘ ricciConnectionCycle := by
      funext s
      fin_cases s <;> rfl
    rw [hv,hs,hc]
  have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
  have hR (v : Fin 2 → RIdx n) :
      ContDiffOn ℝ ∞ (fun w => ricciTensor (h t) c w v) (chartTarget c) :=
    realRicciCoeff_contDiffOn (h t) hh c (v 0) (v 1)
  have hA (v : Fin 3 → RIdx n) := ((covariantD_contDiffOn (h t) hh c
    (ricciTensor (h t) c) hR v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hB (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => B w v) z := hA (v ∘ e)
  have hC (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => C w v) z := hA (v ∘ ricciConnectionCycle)
  have hAB (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => (A w+B w) v) z :=
    (hA v).add (hB v)
  have hABC (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => (A w+B w-C w) v) z :=
    (hAB v).sub (hC v)
  have hD := covariantD_eventuallyEq (h t) c _ _ z heq
  change covariantD (h t) c (lowerConnectionTensor (h t) c
    (fun w => dotChristoffel h c w t)) z=
      covariantD (h t) c (fun w v => -(σ/2)*((A w+B w-C w) v)) z at hD
  rw [covariantD_const_mul_at (h t) c _ z hABC,
    covariantD_sub_at (h t) c _ _ z hAB hC,
    covariantD_add_at (h t) c _ _ z hA hB] at hD
  have hv := congrFun hD ![i,j,k,l]
  change covariantD (h t) c _ z ![i,j,k,l]=
    -(σ/2)*(covariantD (h t) c A z (Fin.cons i ![j,k,l])+
      covariantD (h t) c B z (Fin.cons i ![j,k,l])-
        covariantD (h t) c C z (Fin.cons i ![j,k,l])) at hv
  have hs : ![j,k,l] ∘ e=![k,j,l] := by
    funext s
    fin_cases s <;> simp [e,Equiv.swap_apply_def]
  have hc : ![j,k,l] ∘ ricciConnectionCycle=![l,j,k] := by
    funext s
    fin_cases s <;> rfl
  change covariantD (h t) c _ z ![i,j,k,l]=
    -(σ/2)*(covariantD (h t) c A z (Fin.cons i ![j,k,l])+
      covariantD (h t) c (fun w v => A w (v ∘ e)) z (Fin.cons i ![j,k,l])-
        covariantD (h t) c (fun w v => A w (v ∘ ricciConnectionCycle)) z
          (Fin.cons i ![j,k,l])) at hv
  rw [covariantD_permute_cons,covariantD_permute_cons,hs,hc] at hv
  exact hv

theorem localRealRicciFlow_rmTensor_secondRicci_hasDerivAt
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hx : chartInv c z ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (i j k l : RIdx n) :
    HasDerivAt (fun s => rmTensor (h s) c z ![i,j,k,l])
      (-σ*(∑ p, realRicciCoeff (h t) c z p l*riemannCoeff (h t) c z i j k p)-
        (σ/2)*((covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,j,k,l]+
          covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,k,j,l]-
            covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![i,l,j,k])-
              (covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![j,i,k,l]+
                covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![j,k,i,l]-
                  covariantD (h t) c (covariantD (h t) c (ricciTensor (h t) c)) z ![j,l,i,k]))) t := by
  have hd := localRealRicciFlow_rmTensor_hasDerivAt_lowered h O a b σ hflow c hz hx t ht i j k l
  rw [localRealRicciFlow_covariantD_lowerConnectionTensor h O a b σ hO hflow c hz hx t ht,
    localRealRicciFlow_covariantD_lowerConnectionTensor h O a b σ hO hflow c hz hx t ht] at hd
  convert hd using 1
  ring

end Yau.LeafProofs.L23Aux
