import Yau.LeafProofs.L23ReactionRepresentation
import Yau.LeafProofs.L23JetEvolutionRecurrence

/-! Every original curvature jet residual equals its explicit finite
reaction list. The induction equality holds on an open chart neighborhood. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem jetParabolicTensor_eq_reactionList
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (hx : chartInv c z ∈ O)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (k : ℕ) :
    jetParabolicTensor h c k z t σ=fun v => σ*reactionListEval (h t) c k z v := by
  have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
  induction k generalizing z with
  | zero =>
      change jetParabolicTensor h c 0 z t σ=fun v => σ*jetTermListEval baseTerms (h t) c z v
      rw [baseTerms_eval (h t) c hz]
      funext v
      have hv : v=![v 0,v 1,v 2,v 3] := by funext s; fin_cases s <;> rfl
      rw [hv]
      exact rmTensor_evolution_four h O a b σ hO hflow c hz hx t ht (v 0) (v 1) (v 2) (v 3)
  | succ k ih =>
      have hEq : (fun w => jetParabolicTensor h c k w t σ)=ᶠ[𝓝 z]
          (fun w v => σ*reactionListEval (h t) c k w v) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz,
          (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds (hO.mem_nhds hx)] with w hw hwo
        exact ih hw hwo
      have hRd (u : Fin (4+k) → RIdx n) := ((reactionListEval_contDiffOn (h t) hh c k u).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      have hD := covariantD_eventuallyEq (h t) c _ _ z hEq
      rw [covariantD_const_mul_at (h t) c _ z hRd σ] at hD
      funext V
      let i := V 0
      let v : Fin (4+k) → RIdx n := fun j => V j.succ
      have hv : Fin.cons i v=V := by
        funext s
        refine Fin.cases ?_ (fun j => ?_) s <;> rfl
      rw [←hv]
      have hDp := congrFun hD (Fin.cons i v)
      change covariantD (h t) c (fun w => jetParabolicTensor h c k w t σ) z (Fin.cons i v)=
        σ*covariantD (h t) c (fun w => reactionListEval (h t) c k w) z (Fin.cons i v) at hDp
      rw [jetParabolicTensor_succ h O a b σ hO hflow c hz hx t ht,hDp,
        reactionListEval_succ (h t) hh c k hz,extraTerms_eval (h t) hh c hz]
      ring

theorem jetReactionBound (n k : ℕ) : JetReactionBoundGap n k := by
  refine ⟨reactionConstant n k,reactionConstant_pos n k,?_⟩
  intro M h O a b σ hO hab hσ hflow c z hz hx t ht
  rw [jetParabolicTensor_eq_reactionList h O a b σ hO hflow c hz hx t ht k,
    sqrt_covTensorNormSq_const_mul,abs_of_pos hσ]
  have hN := reactionListEval_norm_le (h t) c k hz
  have hS := jetConvolution_nonneg (h t) c k z
  change σ*Real.sqrt (covTensorNormSq (realMetricFn (h t) c z) (reactionListEval (h t) c k z))≤
    σ*reactionConstant n k*jetConvolution (h t) c k z
  calc
    _≤σ*((2*n : ℕ)*(reactionTermCount k : ℝ)*jetConvolution (h t) c k z) :=
      mul_le_mul_of_nonneg_left hN hσ.le
    _≤_ := by
      unfold reactionConstant
      nlinarith [mul_nonneg hσ.le hS]

end Yau.LeafProofs.L23Aux
