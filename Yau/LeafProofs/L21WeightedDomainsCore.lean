import Yau.LeafProofs.L21WeightedDomainsCompact

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedRowsGraph_real_weak {α β ι : Type*} [Fintype α] [Fintype ι]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K : ℝ) (hK : 0 ≤ K) (src : α → E →L[ℂ] WeightedScalar n K)
    (dst : β → F →L[ℂ] WeightedScalar n K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (x : E) (y : F) (hGraph : (x,y) ∈ weightedRowsGraph K hK src dst v a b ha hb)
    (r : β) (ψ : X n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Metric.ball 0 1) :
    (∫ z, (ψ z : ℂ)*(dst r y : X n → ℂ) z ∂Yau.lebesgueC n) =
      ∫ z, ∑ c, (src c x : X n → ℂ) z*
        Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow v a b r c ψ z ∂Yau.lebesgueC n := by
  let ψC := weightedRealCompactTest ψ hψ hcψ hsψ
  have he := (weightedRowsGraph_mem_iff K hK src dst v a b ha hb (x,y)).mp hGraph r ψC
  simp only [weightedCompactFunctional_apply] at he
  have hTranspose (c : α) (z : X n) : weightedRowTranspose v a b r c ψC z =
      Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow v a b r c ψ z := by
    simp only [weightedRowTranspose,Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow,
      ψC,weightedRealCompactTest,fderiv_ofReal_apply (hψ.differentiable (by simp) z)]
  have hInt (c : α) : Integrable (fun z => weightedRowTranspose v a b r c ψC z*(src c x : X n → ℂ) z)
      (Yau.lebesgueC n) := by
    have hh := locallyL2On_test_integrable Metric.isOpen_ball (weightedScalar_locallyL2On K (src c x))
      (weightedRowTransposeTest v a b ha hb r c ψC)
    change Integrable (fun z => (src c x : X n → ℂ) z*weightedRowTranspose v a b r c ψC z)
      (Yau.lebesgueC n) at hh
    simpa only [mul_comm] using hh
  calc
    _ = ∑ c, ∫ z, weightedRowTranspose v a b r c ψC z*(src c x : X n → ℂ) z ∂Yau.lebesgueC n := he
    _ = ∫ z, ∑ c, weightedRowTranspose v a b r c ψC z*(src c x : X n → ℂ) z ∂Yau.lebesgueC n :=
      (integral_finsetSum _ (fun c _ => hInt c)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      apply Finset.sum_congr rfl
      intro c hc
      rw [hTranspose]
      exact mul_comm _ _


theorem weightedBallMeasure_le_lebesgue (K : ℝ) (hK : 0 ≤ K) :
    weightedBallMeasure n K ≤ Yau.lebesgueC n :=
  (weightedBallMeasure_le_restrict K hK).trans Measure.restrict_le_self

theorem weightedBall_integral_norm_sq_le (K : ℝ) (hK : 0 ≤ K) {u : X n → ℂ}
    (hu : MemLp u 2 (Yau.lebesgueC n)) :
    (∫ x, ‖u x‖^2 ∂weightedBallMeasure n K) ≤ ∫ x, ‖u x‖^2 ∂Yau.lebesgueC n :=
  integral_mono_measure (weightedBallMeasure_le_lebesgue K hK)
    (Eventually.of_forall (fun x => sq_nonneg ‖u x‖)) (hu.integrable_norm_pow (by decide))

theorem weightedBall_graph_error_tendsto (K : ℝ) (hK : 0 ≤ K)
    (f : ℕ → X n → ℂ) (g : X n → ℂ)
    (hMem : ∀ m, MemLp (fun x => f m x-g x) 2 (Yau.lebesgueC n))
    (hLim : Tendsto (fun m => ∫ x, ‖f m x-g x‖^2 ∂Yau.lebesgueC n) atTop (𝓝 0)) :
    (∀ m, MemLp (fun x => f m x-g x) 2 (weightedBallMeasure n K)) ∧
      Tendsto (fun m => ∫ x, ‖f m x-g x‖^2 ∂weightedBallMeasure n K) atTop (𝓝 0) := by
  refine ⟨fun m => (hMem m).mono_measure (weightedBallMeasure_le_lebesgue K hK),?_⟩
  exact squeeze_zero (fun m => integral_nonneg (fun x => sq_nonneg _))
    (fun m => weightedBall_integral_norm_sq_le K hK (hMem m)) hLim

/-- One fixed compact support gives a true joint weighted graph
approximation for every finite complex first-order row system. -/
theorem weightedDomains_fixed_support_graph_approx {α β ι : Type*} [Fintype α] [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) {S : Set (X n)} (hS : IsCompact S) (hSB : S ⊆ Metric.ball 0 1)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (u : X n → α → ℂ) (w : X n → β → ℂ)
    (hu : ∀ c, MemLp (fun x => u x c) 2 (Yau.lebesgueC n))
    (hw : ∀ r, MemLp (fun x => w x r) 2 (Yau.lebesgueC n))
    (hsu : ∀ c, tsupport (fun x => u x c) ⊆ S)
    (hsw : ∀ r, tsupport (fun x => w x r) ⊆ S)
    (hRow : ∀ r (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, (ψ x : ℂ)*w x r ∂Yau.lebesgueC n) =
        ∫ x, ∑ c, u x c*Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow v a b r c ψ x ∂Yau.lebesgueC n) :
    ∃ (L : Set (X n)) (U : ℕ → X n → α → ℂ), IsCompact L ∧ L ⊆ Metric.ball 0 1 ∧
      (∀ m c, ContDiff ℝ ∞ (fun x => U m x c) ∧ tsupport (fun x => U m x c) ⊆ L) ∧
      (∀ c, (∀ m, MemLp (fun x => U m x c-u x c) 2 (weightedBallMeasure n K)) ∧
        Tendsto (fun m => ∫ x, ‖U m x c-u x c‖^2 ∂weightedBallMeasure n K) atTop (𝓝 0)) ∧
      ∀ r, (∀ m, MemLp (fun x => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (U m) x r-w x r)
          2 (weightedBallMeasure n K)) ∧
        Tendsto (fun m => ∫ x,
          ‖Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (U m) x r-w x r‖^2
            ∂weightedBallMeasure n K) atTop (𝓝 0) := by
  obtain ⟨L,U,hL,hLB,hU,hInput,hOutput⟩ :=
    Yau.LeafProofs.L14Aux.exists_fixed_support_complex_firstOrder_graph_approx_norm
      Metric.isOpen_ball hS hSB v a b ha hb u w hu hw hsu hsw hRow
  refine ⟨L,U,hL,hLB,hU,?_,?_⟩
  · intro c
    exact weightedBall_graph_error_tendsto K hK (fun m x => U m x c) (fun x => u x c)
      (hInput c).1 (hInput c).2
  · intro r
    exact weightedBall_graph_error_tendsto K hK
      (fun m x => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (U m) x r)
      (fun x => w x r) (hOutput r).1 (hOutput r).2

end Yau.LeafProofs.L21Aux
