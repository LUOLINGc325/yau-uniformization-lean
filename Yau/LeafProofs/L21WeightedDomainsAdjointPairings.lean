import Yau.LeafProofs.L21WeightedDomainsAdjointTests

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedMaximalFormalTstar_graph_unweighted (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (v : WeightedOneForm n K) (g : WeightedScalar n K) :
    (v,g) ∈ (weightedMaximalFormalTstar K hK A hA).graph ↔
      ∀ ψ : CompactTest (Metric.ball (0 : X n) 1),
        (∫ x, ψ x*g x ∂Yau.lebesgueC n) = ∑ j, ∫ x,
          weightedRowTranspose Yau.realVec (weightedTstarPrincipal A) (weightedTstarZeroOrder K A)
            () j ψ x*(weightedFieldProjection K j v : X n → ℂ) x ∂Yau.lebesgueC n := by
  unfold weightedMaximalFormalTstar
  rw [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (fun y hy => hy ()),weightedRowsGraph_mem_iff]
  simp only [ContinuousLinearMap.id_apply,weightedCompactFunctional_apply]
  constructor
  · exact fun h ψ => h () ψ
  · intro h r ψ
    cases r
    exact h ψ

theorem inner_weightedDualCompactTest (K : ℝ) (hK : 0 ≤ K)
    (ξ : CompactTest (Metric.ball (0 : X n) 1)) (g : WeightedScalar n K) :
    inner ℂ (compactToWeightedScalar K hK ξ) g =
      ∫ x, weightedDualCompactTest K ξ x*g x ∂Yau.lebesgueC n := by
  rw [inner_compactToWeightedScalar]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [weightedDualCompactTest_apply]
  change star (ξ x)*g x*(Real.exp (-boundaryWeight K x) : ℂ) =
    (Real.exp (-boundaryWeight K x) : ℂ)*star (ξ x)*g x
  ring

theorem inner_compactT_weightedDualTest (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (ξ : CompactTest (Metric.ball (0 : X n) 1)) (v : WeightedOneForm n K) :
    inner ℂ ((weightedMaximalT K hK A hA) (weightedCompactTPoint K hK A hA ξ)) v =
      ∑ j, ∫ x, weightedRowTranspose Yau.realVec (weightedTstarPrincipal A) (weightedTstarZeroOrder K A)
        () j (weightedDualCompactTest K ξ) x*(weightedFieldProjection K j v : X n → ℂ) x ∂Yau.lebesgueC n := by
  rw [weightedCompactTPoint_apply_eq,inner_weightedCompactField]
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [] with x
  rw [weightedTstarTranspose_dualTest K A hA ξ j x,weightedStrongRowsTest_apply,weightedTSystemApply_eq_degenerateT]
  change star (degenerateT A ξ x j)*(weightedFieldProjection K j v : X n → ℂ) x*
    (Real.exp (-boundaryWeight K x) : ℂ) =
    (star (degenerateT A ξ x j)*(Real.exp (-boundaryWeight K x) : ℂ))*
      (weightedFieldProjection K j v : X n → ℂ) x
  ring

theorem weightedDualCompactTest_inverse (K : ℝ) (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    weightedDualCompactTest K (weightedDensityInverseTest K (weightedConjugateTest ψ)) = ψ := by
  apply Subtype.ext
  funext x
  change (Real.exp (-boundaryWeight K x) : ℂ)*
    star ((Real.exp (boundaryWeight K x) : ℂ)*star (ψ x)) = ψ x
  rw [star_mul,show star (Real.exp (boundaryWeight K x) : ℂ) =
    (Real.exp (boundaryWeight K x) : ℂ) from Complex.conj_ofReal _,star_star]
  have he : (Real.exp (-boundaryWeight K x) : ℂ)*(Real.exp (boundaryWeight K x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    simp
  calc
    _ = ((Real.exp (-boundaryWeight K x) : ℂ)*(Real.exp (boundaryWeight K x) : ℂ))*ψ x := by ring
    _ = ψ x := by rw [he,one_mul]

/-- The literal maximal formal adjoint is precisely the compact weighted
Hilbert pairing condition. All distribution representatives remain genuine L² classes. -/
theorem weightedMaximalFormalTstar_compact_pairing_iff (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (v : WeightedOneForm n K) (g : WeightedScalar n K) :
    (v,g) ∈ (weightedMaximalFormalTstar K hK A hA).graph ↔
      ∀ ξ : CompactTest (Metric.ball (0 : X n) 1),
        inner ℂ (compactToWeightedScalar K hK ξ) g =
          inner ℂ ((weightedMaximalT K hK A hA) (weightedCompactTPoint K hK A hA ξ)) v := by
  rw [weightedMaximalFormalTstar_graph_unweighted]
  constructor
  · intro h ξ
    rw [inner_weightedDualCompactTest,inner_compactT_weightedDualTest]
    exact h (weightedDualCompactTest K ξ)
  · intro h ψ
    have hh := h (weightedDensityInverseTest K (weightedConjugateTest ψ))
    rw [inner_weightedDualCompactTest,inner_compactT_weightedDualTest,weightedDualCompactTest_inverse] at hh
    exact hh

end Yau.LeafProofs.L21Aux
