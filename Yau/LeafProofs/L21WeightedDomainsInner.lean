import Yau.LeafProofs.L21WeightedDomainsComposition

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedField_inner_eq_sum (K : ℝ) {ι : Type*} [Fintype ι]
    (u v : WeightedField n K ι) :
    inner ℂ u v = ∑ i, inner ℂ (weightedFieldProjection K i u) (weightedFieldProjection K i v) := by
  have hInt (i : ι) : Integrable (fun x => inner ℂ (u x i) (v x i)) (weightedBallMeasure n K) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (weightedFieldProjection K i u) (weightedFieldProjection K i v)).congr
    filter_upwards [weightedFieldProjection_coeFn K i u,weightedFieldProjection_coeFn K i v] with x hx hy
    rw [hx,hy]
  rw [L2.inner_def]
  simp_rw [PiLp.inner_apply]
  rw [integral_finsetSum _ (fun i _ => hInt i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightedFieldProjection_coeFn K i u,weightedFieldProjection_coeFn K i v] with x hx hy
  rw [hx,hy]

theorem weightedCompactField_projection_eq (K : ℝ) (hK : 0 ≤ K)
    {ι : Type*} [Fintype ι] (u : ι → CompactTest (Metric.ball (0 : X n) 1)) (i : ι) :
    weightedFieldProjection K i (weightedCompactField K hK u) = compactToWeightedScalar K hK (u i) := by
  apply Lp.ext
  exact (weightedCompactFieldProjection_rep K hK u i).symm.trans
    (compactToWeightedScalar_coeFn K hK (u i)).symm

theorem inner_weightedCompactField (K : ℝ) (hK : 0 ≤ K)
    {ι : Type*} [Fintype ι] (u : ι → CompactTest (Metric.ball (0 : X n) 1)) (v : WeightedField n K ι) :
    inner ℂ (weightedCompactField K hK u) v =
      ∑ i, ∫ x, star (u i x)*(weightedFieldProjection K i v : X n → ℂ) x*
        (Real.exp (-boundaryWeight K x) : ℂ) ∂Yau.lebesgueC n := by
  rw [weightedField_inner_eq_sum]
  simp_rw [weightedCompactField_projection_eq,inner_compactToWeightedScalar]

theorem weightedCompactTPoint_apply_eq (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA : MatrixSmoothOn A (Metric.ball 0 1))
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    (weightedMaximalT K hK A hA) (weightedCompactTPoint K hK A hA ψ) =
      weightedCompactField K hK (weightedStrongRowsTest Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
        (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const) (fun _ : Unit => ψ)) := by
  apply Lp.ext
  filter_upwards [weightedCompactTPoint_apply_rep K hK A hA ψ,
    weightedCompactField_coeFn K hK (weightedStrongRowsTest Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
      (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const) (fun _ : Unit => ψ))] with x hx hy
  rw [hx,hy]
  ext j
  exact ((weightedStrongRowsTest_apply Yau.realVec (weightedTPrincipal A) (fun _ _ _ => 0)
    (weightedTPrincipal_smooth hA) (fun _ _ => contDiffOn_const) (fun _ : Unit => ψ) j x).trans
    (weightedTSystemApply_eq_degenerateT A ψ x j)).symm

theorem weightedMaximalT_adjoint_of_compact_pairings (K : ℝ) (hK : 0 ≤ K)
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (hA2 : MatrixSmoothOn A (Metric.ball 0 2))
    (v : WeightedOneForm n K) (g : WeightedScalar n K)
    (hPair : ∀ ψ : CompactTest (Metric.ball (0 : X n) 1),
      inner ℂ g (compactToWeightedScalar K hK ψ) = inner ℂ v
        ((weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2))
          (weightedCompactTPoint K hK A (weightedDomains_matrixSmoothOn_ball_one hA2) ψ))) :
    ∃ hv : v ∈ (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint.domain,
      (weightedMaximalT K hK A (weightedDomains_matrixSmoothOn_ball_one hA2)).adjoint ⟨v,hv⟩ = g := by
  let hA := weightedDomains_matrixSmoothOn_ball_one hA2
  let T := weightedMaximalT K hK A hA
  have hAll (u : T.domain) : inner ℂ g (u : WeightedScalar n K) = inner ℂ v (T u) := by
    obtain ⟨ψ,hIn,hOut⟩ := weightedMaximalT_compact_graph_core K hK A hA2 u
    have hL := (tendsto_const_nhds (x := g)).inner hIn (𝕜 := ℂ)
    have hR := (tendsto_const_nhds (x := v)).inner hOut (𝕜 := ℂ)
    exact tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall (fun m => (hPair (ψ m)).symm)))
  have hv := T.mem_adjoint_domain_of_exists v ⟨g,hAll⟩
  exact ⟨hv,T.adjoint_apply_eq (weightedMaximalT_domain_dense K hK A hA) _ hAll⟩

end Yau.LeafProofs.L21Aux
