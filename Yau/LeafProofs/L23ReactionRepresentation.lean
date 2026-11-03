import Yau.LeafProofs.L23ReactionListCalculus
import Yau.LeafProofs.L23ReactionBaseEval
import Yau.LeafProofs.L23ReactionCorrectionEval

/-! The actual Q polynomial and the three correction sums have exactly
the selected finite word representations. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem baseTerms_eval (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    jetTermListEval baseTerms h c z=rmReaction h c z := by
  funext v
  simp only [jetTermListEval,baseTerms,List.map_ofFn,List.sum_ofFn]
  change (∑ j : Fin 11, (baseCoeff j).toReal*(baseWord j).eval
    (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) v)=_
  exact baseWords_sum_eq_rmReaction h c hz v

theorem correctionTerm0_eval (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (k : ℕ) (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    (correctionTerm0 k).eval h c z (Fin.cons i v)=
      -(1/2 : ℝ)*(∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*realRicciCoeff h c z i q*
        rmJet h c (k+1) z (Fin.cons p v)) := by
  change -(1/2 : ℝ)*(correctionWord0 (4+k)).eval (realMetricFn h c z)⁻¹
    (rmTensor h c z) (rmJet h c (k+1) z) (Fin.cons i v)=_
  congr 1
  rw [eval_correctionWord0]
  simp_rw [realRicciCoeff_rmTrace]
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_lhs => rw [sum_four_rotate]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem correctionTerm1_eval (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (k : ℕ) (s : Fin (4+k)) (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    (correctionTerm1 k s).eval h c z (Fin.cons i v)=
      -(∑ a, ∑ b, ∑ p, ∑ q, (realMetricFn h c z)⁻¹ a b*(realMetricFn h c z)⁻¹ p q*
        rmTensor h c z ![i,a,v s,q]*rmJet h c (k+1) z (Fin.cons b (Function.update v s p))) := by
  change (-1 : ℝ)*(correctionWord1 s).eval (realMetricFn h c z)⁻¹
    (rmTensor h c z) (rmJet h c (k+1) z) (Fin.cons i v)=_
  rw [eval_correctionWord1]
  ring

theorem correctionTerm2_eval (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (k : ℕ) (s : Fin (4+k)) (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    (correctionTerm2 k s).eval h c z (Fin.cons i v)=
      (1/2 : ℝ)*(∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*
        covariantD h c (ricciTensor h c) z ![i,v s,q]*rmJet h c k z (Function.update v s p)) := by
  change (1/2 : ℝ)*(correctionWord2 s).eval (realMetricFn h c z)⁻¹
    (covariantD h c (rmTensor h c) z) (rmJet h c k z) (Fin.cons i v)=_
  congr 1
  rw [eval_correctionWord2]
  simp_rw [covariantD_ricciTensor_trace h hh c hz]
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_lhs => rw [sum_four_rotate]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem extraTerms_eval (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (k : ℕ) (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    jetTermListEval (extraTerms k) h c z (Fin.cons i v)=
      -(1/2 : ℝ)*(∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*realRicciCoeff h c z i q*
        rmJet h c (k+1) z (Fin.cons p v))-
      (∑ a, ∑ b, ∑ s : Fin (4+k), ∑ p, ∑ q,
        (realMetricFn h c z)⁻¹ a b*(realMetricFn h c z)⁻¹ p q*
          rmTensor h c z ![i,a,v s,q]*rmJet h c (k+1) z (Fin.cons b (Function.update v s p)))+
      (1/2 : ℝ)*(∑ s : Fin (4+k), ∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*
        covariantD h c (ricciTensor h c) z ![i,v s,q]*rmJet h c k z (Function.update v s p)) := by
  have h1 : (∑ s : Fin (4+k), (correctionTerm1 k s).eval h c z (Fin.cons i v))=
      -(∑ a, ∑ b, ∑ s : Fin (4+k), ∑ p, ∑ q,
        (realMetricFn h c z)⁻¹ a b*(realMetricFn h c z)⁻¹ p q*
          rmTensor h c z ![i,a,v s,q]*rmJet h c (k+1) z (Fin.cons b (Function.update v s p))) := by
    simp_rw [correctionTerm1_eval]
    simp only [Finset.sum_neg_distrib]
    apply congrArg (fun x : ℝ => -x)
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
  have h2 : (∑ s : Fin (4+k), (correctionTerm2 k s).eval h c z (Fin.cons i v))=
      (1/2 : ℝ)*(∑ s : Fin (4+k), ∑ p, ∑ q, (realMetricFn h c z)⁻¹ p q*
        covariantD h c (ricciTensor h c) z ![i,v s,q]*rmJet h c k z (Function.update v s p)) := by
    simp_rw [correctionTerm2_eval h hh c hz]
    simp only [Finset.mul_sum]
  unfold extraTerms
  rw [jetTermListEval_cons,jetTermListEval_append]
  simp only [Pi.add_apply,jetTermListEval,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rw [correctionTerm0_eval,h1,h2]
  ring

end Yau.LeafProofs.L23Aux
