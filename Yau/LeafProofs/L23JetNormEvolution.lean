import Yau.LeafProofs.L23ReactionIdentity
import Yau.LeafProofs.L23JetSpaceTimeCalculus
import Yau.LeafProofs.L23TensorTimeBound

/-! The actual scalar Bernstein evolution of the original curvature jets. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem jetParabolicTensor_norm_le
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hσ : 0 ≤ σ) (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (hx : chartInv c z ∈ O)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (k : ℕ) :
    Real.sqrt (covTensorNormSq (realMetricFn (h t) c z) (jetParabolicTensor h c k z t σ))≤
      σ*reactionConstant n k*jetConvolution (h t) c k z := by
  rw [jetParabolicTensor_eq_reactionList h O a b σ hO hflow c hz hx t ht,
    sqrt_covTensorNormSq_const_mul,abs_of_nonneg hσ]
  have hN := reactionListEval_norm_le (h t) c k hz
  have hS := jetConvolution_nonneg (h t) c k z
  calc
    _≤σ*((2*n : ℕ)*(reactionTermCount k : ℝ)*jetConvolution (h t) c k z) :=
      mul_le_mul_of_nonneg_left hN hσ
    _≤_ := by unfold reactionConstant; nlinarith [mul_nonneg hσ hS]

theorem jetSq_flowOp_le_raw
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ)
    (hσ : 0 ≤ σ) (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (k : ℕ) :
    flowOp h σ (fun y s => jetSq (h s) k y) x t≤
      -σ*jetSq (h t) (k+1) x+
        2*Real.sqrt (jetSq (h t) k x)*Real.sqrt
          (covTensorNormSq (realMetricFn (h t) x (chartPt x x))
            (jetParabolicTensor h x k (chartPt x x) t σ))+
        σ*(4+k : ℕ)*(2*n : ℕ)*Real.sqrt (jetSq (h t) 0 x)*jetSq (h t) k x := by
  let G := realMetricFn (h t) x (chartPt x x)
  let A := rmJet (h t) x k (chartPt x x)
  let A' : CovTensor n (4+k) := fun v => deriv (fun s => rmJet (h s) x k (chartPt x x) v) t
  let P := jetParabolicTensor h x k (chartPt x x) t σ
  let J : Matrix (RIdx n) (RIdx n) ℝ := fun i j => σ*∑ p, ∑ q,
    G⁻¹ i p*realRicciCoeff (h t) x (chartPt x x) p q*G⁻¹ q j
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
  have hG : G.PosDef := L12Aux.realMetricFn_posDef (h t) x _ hz
  have hAd (v : Fin (4+k) → RIdx n) :
      HasDerivAt (fun s => rmJet (h s) x k (chartPt x x) v) (A' v) t := by
    have hJ : ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ => rmJet (h p.2) x k p.1 v)
        (chartPt x x,t) := (rmJetFamilySmooth_joint h a b hflow.1 x k v).contDiffAt
      ((isOpen_flowChartDomain x a b).mem_nhds ⟨hz,ht⟩)
    have hc := hJ.comp t (contDiffAt_const.prodMk contDiffAt_id)
    exact (hc.differentiableAt (by simp)).hasDerivAt
  have htime := localRealRicciFlow_covTensorNormSq_hasDerivAt h O a b σ hflow x hx t ht
    (fun s => rmJet (h s) x k (chartPt x x)) A' hAd
  have hT : deriv (fun s => jetSq (h s) k x) t=
      2*covTensorPair G A' A+tensorMetricVariation G⁻¹ J A A := htime.deriv
  have hL : realLap (h t) (jetSq (h t) k) x=
      2*covTensorPair G A (roughLap (h t) x (rmJet (h t) x k) (chartPt x x))+
        2*jetSq (h t) (k+1) x := realLap_jetSq (h t) hh k x
  have hP : P=(fun v => A' v-(σ/2)*roughLap (h t) x (rmJet (h t) x k) (chartPt x x) v) := rfl
  have hp : covTensorPair G A P=covTensorPair G A A'-
      (σ/2)*covTensorPair G A (roughLap (h t) x (rmJet (h t) x k) (chartPt x x)) := by
    rw [hP,covTensorPair_sub_right,covTensorPair_mul_right]
  have hSym := covTensorPair_symm G hG A' A
  have hId : flowOp h σ (fun y s => jetSq (h s) k y) x t=
      2*covTensorPair G A P-σ*jetSq (h t) (k+1) x+tensorMetricVariation G⁻¹ J A A := by
    unfold flowOp
    rw [hT,hL,hSym]
    nlinarith [hp]
  have hJ : J=σ•((G⁻¹*chartRealRicciMatrix (h t) x (chartPt x x))*G⁻¹) := by
    ext i j
    simp only [J,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,chartRealRicciMatrix,
      Finset.sum_mul,Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
  have hV : tensorMetricVariation G⁻¹ J A A≤
      σ*(4+k : ℕ)*(2*n : ℕ)*Real.sqrt (jetSq (h t) 0 x)*jetSq (h t) k x := by
    rw [hJ]
    exact ricci_tensorMetricVariation_le (h t) hh x hz σ hσ A
  have hPair : covTensorPair G A P≤Real.sqrt (jetSq (h t) k x)*
      Real.sqrt (covTensorNormSq G P) := covTensorPair_le_sqrt G hG A P
  rw [hId]
  change 2*covTensorPair G A P-σ*jetSq (h t) (k+1) x+tensorMetricVariation G⁻¹ J A A≤
    -σ*jetSq (h t) (k+1) x+2*Real.sqrt (jetSq (h t) k x)*Real.sqrt (covTensorNormSq G P)+_
  linarith [hPair,hV]

theorem jetSq_flowOp_le
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hσ : 0 ≤ σ) (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b) (k : ℕ) :
    flowOp h σ (fun y s => jetSq (h s) k y) x t≤
      -σ*jetSq (h t) (k+1) x+σ*jetEvolutionConstant n k*jetReactionSum (h t) k x := by
  have hraw := jetSq_flowOp_le_raw h O a b σ hσ hflow x hx t ht k
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hinv : chartInv x (chartPt x x)=x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hx' : chartInv x (chartPt x x) ∈ O := by rw [hinv]; exact hx
  have hP := jetParabolicTensor_norm_le h O a b σ hO hσ hflow x hz hx' t ht k
  have hCross : 2*Real.sqrt (jetSq (h t) k x)*Real.sqrt
      (covTensorNormSq (realMetricFn (h t) x (chartPt x x))
        (jetParabolicTensor h x k (chartPt x x) t σ))≤
      2*σ*reactionConstant n k*jetReactionSum (h t) k x := by
    calc
      _≤2*Real.sqrt (jetSq (h t) k x)*
          (σ*reactionConstant n k*jetConvolution (h t) x k (chartPt x x)) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      _=2*σ*reactionConstant n k*
          (jetConvolution (h t) x k (chartPt x x)*Real.sqrt (jetSq (h t) k x)) := by ring
      _=_ := by rw [jetConvolution_mul_sqrt]
  have hM : σ*(4+k : ℕ)*(2*n : ℕ)*Real.sqrt (jetSq (h t) 0 x)*jetSq (h t) k x≤
      σ*(4+k : ℕ)*(2*n : ℕ)*jetReactionSum (h t) k x := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (metricReaction_le_jetReactionSum (h t) k x)
      (show 0 ≤ σ*(4+k : ℕ)*(2*n : ℕ) by positivity)
  calc
    _≤-σ*jetSq (h t) (k+1) x+2*σ*reactionConstant n k*jetReactionSum (h t) k x+
        σ*(4+k : ℕ)*(2*n : ℕ)*jetReactionSum (h t) k x := by linarith [hraw,hCross,hM]
    _=_ := by unfold jetEvolutionConstant; ring

end Yau.LeafProofs.L23Aux
