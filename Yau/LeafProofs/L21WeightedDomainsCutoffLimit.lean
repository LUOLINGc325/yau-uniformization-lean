import Yau.LeafProofs.L21WeightedDomainsConvergence

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem weightedDomains_L2_add_error_tendsto (μ : Measure (X n))
    (f g : ℕ → X n → ℂ) (hf : ∀ m, MemLp (f m) 2 μ) (hg : ∀ m, MemLp (g m) 2 μ)
    (hF : Tendsto (fun m => ∫ x, ‖f m x‖^2 ∂μ) atTop (𝓝 0))
    (hG : Tendsto (fun m => ∫ x, ‖g m x‖^2 ∂μ) atTop (𝓝 0)) :
    (∀ m, MemLp (fun x => f m x+g m x) 2 μ) ∧
      Tendsto (fun m => ∫ x, ‖f m x+g m x‖^2 ∂μ) atTop (𝓝 0) := by
  have htF : Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 (0 : Lp ℂ 2 μ)) := by
    simpa only [Pi.zero_apply,sub_zero,MemLp.toLp_zero] using
      complex_toLp_tendsto_of_integral_norm_sq f (0 : X n → ℂ) hf MemLp.zero (by simpa only [Pi.zero_apply,sub_zero] using hF)
  have htG : Tendsto (fun m => (hg m).toLp (g m)) atTop (𝓝 (0 : Lp ℂ 2 μ)) := by
    simpa only [Pi.zero_apply,sub_zero,MemLp.toLp_zero] using
      complex_toLp_tendsto_of_integral_norm_sq g (0 : X n → ℂ) hg MemLp.zero (by simpa only [Pi.zero_apply,sub_zero] using hG)
  have hMem (m : ℕ) := (hf m).add (hg m)
  refine ⟨hMem,?_⟩
  have hLim := complex_integral_norm_sq_tendsto_of_toLp_tendsto
    (fun m x => f m x+g m x) (0 : X n → ℂ) hMem MemLp.zero (by
      change Tendsto (fun m => (hf m).toLp (f m)+(hg m).toLp (g m)) atTop (𝓝 (0 : Lp ℂ 2 μ))
      simpa only [zero_add] using htF.add htG)
  simpa only [Pi.zero_apply,sub_zero] using hLim

theorem weightedDomains_L2_finset_error_tendsto {ι : Type*} (μ : Measure (X n))
    (s : Finset ι) (f : ι → ℕ → X n → ℂ)
    (hf : ∀ i m, MemLp (f i m) 2 μ)
    (hF : ∀ i, Tendsto (fun m => ∫ x, ‖f i m x‖^2 ∂μ) atTop (𝓝 0)) :
    (∀ m, MemLp (fun x => ∑ i ∈ s, f i m x) 2 μ) ∧
      Tendsto (fun m => ∫ x, ‖∑ i ∈ s, f i m x‖^2 ∂μ) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero] using
      (show (∀ m : ℕ, MemLp (fun _ : X n => (0 : ℂ)) 2 μ) ∧
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from ⟨fun _ => MemLp.zero,tendsto_const_nhds⟩)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using weightedDomains_L2_add_error_tendsto μ
      (f i) (fun m x => ∑ j ∈ s, f j m x) (hf i) ih.1 (hF i) ih.2

/-- The complete cutoff output error tends to zero, with the original
zeroth-order rows absent from the commutator. -/
theorem weightedDomains_cutoff_output_tendsto {α β ι : Type*} [Fintype α] [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K) (v : ι → X n)
    (a p : β → α → ι → X n → ℂ)
    (hFactor : ∀ r c i x, a r c i x = (rho x : ℂ)*p r c i x)
    (hp : ∀ r c i, ContinuousOn (p r c i) (Metric.ball 0 1))
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ r c i x, x ∈ Metric.ball (0 : X n) 1 → ‖p r c i x‖ ≤ C)
    (u : X n → α → ℂ) (w : X n → β → ℂ)
    (hu : ∀ c, MemLp (fun x => u x c) 2 (weightedBallMeasure n K))
    (hw : ∀ r, MemLp (fun x => w x r) 2 (weightedBallMeasure n K)) (r : β) :
    (∀ m, MemLp (fun x => Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a
      (boundaryCutoff m) u w x r-w x r) 2 (weightedBallMeasure n K)) ∧
      Tendsto (fun m => ∫ x, ‖Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a
        (boundaryCutoff m) u w x r-w x r‖^2 ∂weightedBallMeasure n K) atTop (𝓝 0) := by
  let f : α × ι → ℕ → X n → ℂ := fun q m x =>
    p r q.1 q.2 x*((rho x*fderiv ℝ (boundaryCutoff m) x (v q.2) : ℝ) : ℂ)*u x q.1
  have hEach (q : α × ι) := weightedBoundaryCutoff_principal_error_tendsto K hK
    (hp r q.1 q.2) hC (hBound r q.1 q.2) (hu q.1) (v q.2)
  have hSum := weightedDomains_L2_finset_error_tendsto (weightedBallMeasure n K) Finset.univ f
    (fun q => (hEach q).1) (fun q => (hEach q).2)
  have hValue := weightedBoundaryCutoff_error_tendsto K (hw r)
  have hAdd := weightedDomains_L2_add_error_tendsto (weightedBallMeasure n K)
    (fun m x => (boundaryCutoff m x : ℂ)*w x r-w x r)
    (fun m x => ∑ q, f q m x) hValue.1 hSum.1 hValue.2 hSum.2
  have hPoint (m : ℕ) (x : X n) :
      Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r-w x r =
        (boundaryCutoff m x : ℂ)*w x r-w x r+∑ q, f q m x := by
    have hSums : (∑ c, ∑ i, (fderiv ℝ (boundaryCutoff m) x (v i) : ℂ)*a r c i x*u x c) =
        ∑ c, ∑ i, p r c i x*((rho x*fderiv ℝ (boundaryCutoff m) x (v i) : ℝ) : ℂ)*u x c := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro i hi
      rw [hFactor,Complex.ofReal_mul]
      ring
    simp only [Yau.LeafProofs.L14Aux.localizedComplexSystemOutput,Fintype.sum_prod_type,f]
    rw [hSums]
    ring
  constructor
  · intro m
    simpa only [hPoint] using hAdd.1 m
  · simpa only [hPoint] using hAdd.2

end Yau.LeafProofs.L21Aux
