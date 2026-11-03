import Yau.LeafProofs.L23RoughLapCommutatorRicci

/-! The exact all-rank Ricci-flow recurrence after contracted Bianchi and
the true time-connection variation cancel their common derivative terms. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem ricciFlow_commutator_cancellation {S P Q : Type*}
    [Fintype S] [Fintype P] [Fintype Q]
    (σ : ℝ) (H : P → Q → ℝ) (X Y Z : S → Q → ℝ) (A : S → P → ℝ) :
    -(σ/2)*(∑ s, ∑ p, ∑ q, H p q*(Y s q-Z s q)*A s p)-
      (∑ s, ∑ p, (-(σ/2)*∑ q, H p q*(X s q+Y s q-Z s q))*A s p)=
      (σ/2)*∑ s, ∑ p, ∑ q, H p q*X s q*A s p := by
  simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

variable {n r : ℕ} {M : ComplexManifold n}

theorem tensorFlowOperator_covariantD_ricciFlow
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (c : M.Carrier) (A : ℝ → ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => A p.2 p.1 v)
      (flowChartDomain c a b))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (hx : chartInv c z ∈ O)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (i : RIdx n) (v : Fin r → RIdx n) :
    tensorFlowOperator h c (fun s => covariantD (h s) c (A s)) σ t z (Fin.cons i v)=
      covariantD (h t) c (tensorFlowOperator h c A σ t) z (Fin.cons i v)-
        (σ/2)*(∑ p, ∑ q, (realMetricFn (h t) c z)⁻¹ p q*realRicciCoeff (h t) c z i q*
          covariantD (h t) c (A t) z (Fin.cons p v))-
        σ*(∑ x, ∑ y, ∑ s : Fin r, ∑ p,
          (realMetricFn (h t) c z)⁻¹ x y*riemannCoeff (h t) c z i x (v s) p*
            covariantD (h t) c (A t) z (Fin.cons y (Function.update v s p)))+
        (σ/2)*(∑ s : Fin r, ∑ p, ∑ q, (realMetricFn (h t) c z)⁻¹ p q*
          covariantD (h t) c (ricciTensor (h t) c) z ![i,v s,q]*A t z (Function.update v s p)) := by
  have hh := metricFamilySmooth_slice h hflow.1 ⟨ht.1.le,ht.2.le⟩
  have hs := tensorFamilySmooth_slice c a b A hA t ht
  have hspatial := covariantD_roughLap_commutator_ricci (h t) hh c (A t) hs hz i v
  have hdot (s : Fin r) (p : RIdx n) : dotChristoffel h c z t p i (v s)=
      -(σ/2)*∑ q, (realMetricFn (h t) c z)⁻¹ p q*
        (covariantD (h t) c (ricciTensor (h t) c) z ![i,v s,q]+
          covariantD (h t) c (ricciTensor (h t) c) z ![v s,i,q]-
            covariantD (h t) c (ricciTensor (h t) c) z ![q,i,v s]) :=
    (localRealRicciFlow_christoffel_hasDerivAt_inChart h O a b σ hO hflow c hz hx t ht p i (v s)).deriv
  have hcancel := ricciFlow_commutator_cancellation σ
    (fun p q => (realMetricFn (h t) c z)⁻¹ p q)
    (fun s q => covariantD (h t) c (ricciTensor (h t) c) z ![i,v s,q])
    (fun s q => covariantD (h t) c (ricciTensor (h t) c) z ![v s,i,q])
    (fun s q => covariantD (h t) c (ricciTensor (h t) c) z ![q,i,v s])
    (fun s p => A t z (Function.update v s p))
  have hdotSum : (∑ s : Fin r, ∑ p, dotChristoffel h c z t p i (v s)*A t z (Function.update v s p))=
      ∑ s : Fin r, ∑ p, (-(σ/2)*∑ q, (realMetricFn (h t) c z)⁻¹ p q*
        (covariantD (h t) c (ricciTensor (h t) c) z ![i,v s,q]+
          covariantD (h t) c (ricciTensor (h t) c) z ![v s,i,q]-
            covariantD (h t) c (ricciTensor (h t) c) z ![q,i,v s]))*A t z (Function.update v s p) := by
    simp_rw [hdot]
  rw [←hdotSum] at hcancel
  rw [tensorFlowOperator_covariantD_raw h a b σ hflow.1 c A hA hz t ht,hspatial]
  nlinarith [hcancel]

end Yau.LeafProofs.L23Aux
