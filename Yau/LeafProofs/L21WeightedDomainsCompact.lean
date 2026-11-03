import Yau.LeafProofs.L21WeightedDomainsStrong

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def weightedStrongRowsTest {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (u : α → CompactTest (Metric.ball (0 : X n) 1)) (r : β) :
    CompactTest (Metric.ball (0 : X n) 1) :=
  ∑ c, ((∑ i, weightedLocalMultiplierTest (ha r c i) (directionalTest (u c) (v i)))+
    weightedLocalMultiplierTest (hb r c) (u c))

theorem weightedStrongRowsTest_apply {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (u : α → CompactTest (Metric.ball (0 : X n) 1)) (r : β) (x : X n) :
    weightedStrongRowsTest v a b ha hb u r x =
      Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (fun y c => u c y) x r := by
  simp [weightedStrongRowsTest,weightedLocalMultiplierTest,directionalTest,
    Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply]


def weightedCompactFieldFn {ι : Type*} [Fintype ι]
    (u : ι → CompactTest (Metric.ball (0 : X n) 1)) (x : X n) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => u i x)

theorem weightedCompactField_memLp (K : ℝ) (hK : 0 ≤ K) {ι : Type*} [Fintype ι]
    (u : ι → CompactTest (Metric.ball (0 : X n) 1)) :
    MemLp (weightedCompactFieldFn u) 2 (weightedBallMeasure n K) := by
  apply MemLp.of_eval_piLp
  intro i
  exact compactTest_weightedBall_memLp K hK (u i)

def weightedCompactField (K : ℝ) (hK : 0 ≤ K) {ι : Type*} [Fintype ι]
    (u : ι → CompactTest (Metric.ball (0 : X n) 1)) : WeightedField n K ι :=
  (weightedCompactField_memLp K hK u).toLp (weightedCompactFieldFn u)

theorem weightedCompactField_coeFn (K : ℝ) (hK : 0 ≤ K) {ι : Type*} [Fintype ι]
    (u : ι → CompactTest (Metric.ball (0 : X n) 1)) :
    (weightedCompactField K hK u : X n → EuclideanSpace ℂ ι) =ᵐ[weightedBallMeasure n K]
      weightedCompactFieldFn u :=
  (weightedCompactField_memLp K hK u).coeFn_toLp

theorem weightedCompactFieldProjection_rep (K : ℝ) (hK : 0 ≤ K) {ι : Type*} [Fintype ι]
    (u : ι → CompactTest (Metric.ball (0 : X n) 1)) (i : ι) :
    (fun x => u i x) =ᵐ[weightedBallMeasure n K]
      (weightedFieldProjection K i (weightedCompactField K hK u) : X n → ℂ) := by
  filter_upwards [weightedFieldProjection_coeFn K i (weightedCompactField K hK u),
    weightedCompactField_coeFn K hK u] with x hx hRep
  exact (congrArg (fun z : EuclideanSpace ℂ ι => z i) hRep).symm.trans hx.symm

theorem weightedTSystemApply_eq_degenerateT
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (u : X n → ℂ) (x : X n) (j : Fin n) :
    Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply Yau.realVec (weightedTPrincipal A)
      (fun _ _ _ => 0) (fun y (_ : Unit) => u y) x j = degenerateT A u x j := by
  simp only [Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply,Fintype.sum_unique,
    zero_mul,add_zero,weightedTPrincipal,degenerateT,scaledGraphD,dbarA_eq_real_rows,Finset.mul_sum,mul_assoc]

/-- Every genuine scalar compact test belongs to the actual maximal T
and has the literal pointwise rho-scaled output as its L² representative. -/
theorem weightedCompactT_graph (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    ∃ f : WeightedOneForm n K,
      (compactToWeightedScalar K hK ψ,f) ∈ (weightedMaximalT K hK A hA).graph ∧
      (f : X n → X n) =ᵐ[weightedBallMeasure n K]
        (fun x => WithLp.toLp 2 (degenerateT A ψ x)) := by
  let out := weightedStrongRowsTest Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
    (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const) (fun _ : Unit => ψ)
  refine ⟨weightedCompactField K hK out,?_,?_⟩
  · unfold weightedMaximalT
    rw [weightedMaximalRows_graph _ _ _ _ _ _ _ _ _ (weightedField_eq_zero_of_projections K)]
    apply weightedRowsGraph_of_smooth_representatives K hK _ _ _ _ _ _ _
      (compactToWeightedScalar K hK ψ) (weightedCompactField K hK out) (fun x (_ : Unit) => ψ x)
    · intro c
      exact ψ.property.1.contDiffOn
    · intro c
      exact (compactToWeightedScalar_coeFn K hK ψ).symm
    · intro j
      have hh := weightedCompactFieldProjection_rep K hK out j
      simpa only [out,weightedStrongRowsTest_apply] using hh
  · apply (weightedCompactField_coeFn K hK out).trans
    filter_upwards [] with x
    ext j
    exact (weightedStrongRowsTest_apply Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
      (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const) (fun _ : Unit => ψ) j x).trans
      (weightedTSystemApply_eq_degenerateT A ψ x j)

theorem weightedCompactT_mem_domain (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    compactToWeightedScalar K hK ψ ∈ (weightedMaximalT K hK A hA).domain := by
  obtain ⟨f,hGraph,hRep⟩ := weightedCompactT_graph K hK A hA ψ
  obtain ⟨u,hu,he⟩ := (LinearPMap.mem_graph_iff (weightedMaximalT K hK A hA)).mp hGraph
  change (u : WeightedScalar n K) = compactToWeightedScalar K hK ψ at hu
  rw [← hu]
  exact u.property

theorem weightedMaximalT_domain_dense (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1)) :
    Dense ((weightedMaximalT K hK A hA).domain : Set (WeightedScalar n K)) := by
  have hSpan : Submodule.span ℂ (range (compactToWeightedScalar (n := n) K hK)) ≤
      (weightedMaximalT K hK A hA).domain := by
    apply Submodule.span_le.mpr
    rintro x ⟨ψ,rfl⟩
    exact weightedCompactT_mem_domain K hK A hA ψ
  exact Dense.mono hSpan (weightedCompactScalar_span_dense K hK)

end Yau.LeafProofs.L21Aux
