import Yau.LeafProofs.L23TensorFlowRecurrence

/-! The exact recurrence for the original rmJet and parabolic residual. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem jetParabolicTensor_succ_upper
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (hx : chartInv c z ∈ O)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (k : ℕ) (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    jetParabolicTensor h c (k+1) z t σ (Fin.cons i v)=
      covariantD (h t) c (fun w => jetParabolicTensor h c k w t σ) z (Fin.cons i v)-
        (σ/2)*(∑ p, ∑ q, (realMetricFn (h t) c z)⁻¹ p q*realRicciCoeff (h t) c z i q*
          rmJet (h t) c (k+1) z (Fin.cons p v))-
        σ*(∑ x, ∑ y, ∑ s : Fin (4+k), ∑ p,
          (realMetricFn (h t) c z)⁻¹ x y*riemannCoeff (h t) c z i x (v s) p*
            rmJet (h t) c (k+1) z (Fin.cons y (Function.update v s p)))+
        (σ/2)*(∑ s : Fin (4+k), ∑ p, ∑ q, (realMetricFn (h t) c z)⁻¹ p q*
          covariantD (h t) c (ricciTensor (h t) c) z ![i,v s,q]*
            rmJet (h t) c k z (Function.update v s p)) := by
  exact tensorFlowOperator_covariantD_ricciFlow h O a b σ hO hflow c
    (fun s => rmJet (h s) c k) (rmJetFamilySmooth_joint h a b hflow.1 c k) hz hx t ht i v

theorem jetParabolicTensor_succ
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (hx : chartInv c z ∈ O)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (k : ℕ) (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    jetParabolicTensor h c (k+1) z t σ (Fin.cons i v)=
      covariantD (h t) c (fun w => jetParabolicTensor h c k w t σ) z (Fin.cons i v)-
        (σ/2)*(∑ p, ∑ q, (realMetricFn (h t) c z)⁻¹ p q*realRicciCoeff (h t) c z i q*
          rmJet (h t) c (k+1) z (Fin.cons p v))-
        σ*(∑ x, ∑ y, ∑ s : Fin (4+k), ∑ p, ∑ q,
          (realMetricFn (h t) c z)⁻¹ x y*(realMetricFn (h t) c z)⁻¹ p q*
            rmTensor (h t) c z ![i,x,v s,q]*
              rmJet (h t) c (k+1) z (Fin.cons y (Function.update v s p)))+
        (σ/2)*(∑ s : Fin (4+k), ∑ p, ∑ q, (realMetricFn (h t) c z)⁻¹ p q*
          covariantD (h t) c (ricciTensor (h t) c) z ![i,v s,q]*
            rmJet (h t) c k z (Function.update v s p)) := by
  have hK : (∑ x, ∑ y, ∑ s : Fin (4+k), ∑ p,
      (realMetricFn (h t) c z)⁻¹ x y*riemannCoeff (h t) c z i x (v s) p*
        rmJet (h t) c (k+1) z (Fin.cons y (Function.update v s p)))=
      ∑ x, ∑ y, ∑ s : Fin (4+k), ∑ p, ∑ q,
        (realMetricFn (h t) c z)⁻¹ x y*(realMetricFn (h t) c z)⁻¹ p q*
          rmTensor (h t) c z ![i,x,v s,q]*
            rmJet (h t) c (k+1) z (Fin.cons y (Function.update v s p)) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro p _
    rw [riemannCoeff_raise_last (h t) c hz,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [jetParabolicTensor_succ_upper h O a b σ hO hflow c hz hx t ht,hK]

end Yau.LeafProofs.L23Aux
