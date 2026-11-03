import Yau.LeafProofs.L03HodgeBufferedSystem
import Yau.LeafProofs.L03MollifierSupport
import Yau.LeafProofs.L03DivergenceResidualL2
import Yau.LeafProofs.L03DivergenceEnergy
import Yau.LeafProofs.L03CompactGradientLimits

open MeasureTheory Filter Module
open scoped Topology ContDiff Convolution

noncomputable section

namespace Yau.LeafProofs.L03.HodgeDivergenceWeak

variable {n k : ℕ} {M : ComplexManifold n}

/-- The actual rough Hodge deficiency field has genuine compact chart
regularizations whose values converge in L² and whose true directional
derivatives are L² Cauchy. Every coefficient, buffer and mollifier datum
is constructed internally; no H¹ premise is imposed on the raw field. -/
theorem exists_localized_smooth_gradient_cauchy {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ∃ K : Set (ComplexVector n), IsCompact K ∧ K ⊆ chartTarget x ∧
      ∃ U : ℕ → ComplexVector n → α → ℝ,
      (∀ m c, ContDiff ℝ ∞ (fun z => U m z c)) ∧
      (∀ m c, tsupport (fun z => U m z c) ⊆ K) ∧
      (∀ c, Tendsto (fun m => ∫ z, ‖U m z c - localizedInput x b χ A z c‖ ^ 2
        ∂lebesgueC n) atTop (𝓝 0)) ∧
      Tendsto (fun p : ℕ × ℕ => ∫ z, DivergenceEnergy.gradientSq (realModelBasis n)
        (fun y c => U p.1 y c - U p.2 y c) z ∂lebesgueC n) atTop (𝓝 0) := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  letI : (lebesgueC n).IsNegInvariant := by rw [lebesgueC_eq_volume]; infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  letI : SigmaFinite (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  obtain ⟨Ω, hΩ, hχΩ, hcΩ, hΩO, θ, hθ, hcθ, hθO, hθone, ha, hB, hC, hweak, ell, hell, hcoercive⟩ :=
    exists_buffered_localized_divergence_system g μ hμ A hmax x b χ hχ hcχ hχO
  let ae := fun r c i j z => θ z * a g.form x b r c i j z
  let Be := fun r c i z => θ z * B g.form x b r c i z
  let Ce := fun r c z => θ z * C g.form x b r c z
  let u := localizedInput x b χ A
  let F0 := localizedValue g.form x b χ A
  let F := localizedFlux g.form x b χ A
  have hm := localized_data_memLp g μ hμ A hmax.1 x b χ hχ hcχ hχO
  have hs := localized_data_support g.form x b χ A
  have hcu (c : α) : HasCompactSupport (fun z => u z c) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (hs.1 c)
  have hcF0 (r : α) : HasCompactSupport (fun z => F0 z r) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (hs.2.1 r)
  have hcF (r : α) (i : RIdx n) : HasCompactSupport (fun z => F z r i) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (hs.2.2 r i)
  have hui (c : α) : Integrable (fun z => u z c) (lebesgueC n) :=
    memLp_two_compact_integrable (lebesgueC n) _ (hm.1 c) (hcu c)
  have hF0i (r : α) : Integrable (fun z => F0 z r) (lebesgueC n) :=
    memLp_two_compact_integrable (lebesgueC n) _ (hm.2.1 r) (hcF0 r)
  have hFi (r : α) (i : RIdx n) : Integrable (fun z => F z r i) (lebesgueC n) :=
    memLp_two_compact_integrable (lebesgueC n) _ (hm.2.2 r i) (hcF r i)
  choose Ac Kc hAc hKc using fun r c i j => compact_contDiff_coefficient_bounds
    (ae r c i j) (ha r c i j) hcθ.mul_right
  choose Bc Kb hBc hKb using fun r c i => compact_contDiff_coefficient_bounds
    (Be r c i) (hB r c i) hcθ.mul_right
  choose Cc Kd hCc hKd using fun r c => compact_contDiff_coefficient_bounds
    (Ce r c) (hC r c) hcθ.mul_right
  let b0 : ℝ := ∑ p : α × α × RIdx n, max (Bc p.1 p.2.1 p.2.2) 0
  let c0 : ℝ := ∑ p : α × α, max (Cc p.1 p.2) 0
  have hb0 : 0 ≤ b0 := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hboundB (z : ComplexVector n) (r c : α) (i : RIdx n) : |Be r c i z| ≤ b0 := by
    have hp : max (Bc r c i) 0 ≤ b0 :=
      Finset.single_le_sum (f := fun p : α × α × RIdx n => max (Bc p.1 p.2.1 p.2.2) 0)
        (fun _ _ => le_max_right _ _) (Finset.mem_univ (r, c, i))
    exact (show |Be r c i z| ≤ Bc r c i by simpa only [Real.norm_eq_abs] using hBc r c i z).trans
      ((le_max_left _ _).trans hp)
  have hboundC (z : ComplexVector n) (r c : α) : |Ce r c z| ≤ c0 := by
    have hp : max (Cc r c) 0 ≤ c0 :=
      Finset.single_le_sum (f := fun p : α × α => max (Cc p.1 p.2) 0)
        (fun _ _ => le_max_right _ _) (Finset.mem_univ (r, c))
    exact (show |Ce r c z| ≤ Cc r c by simpa only [Real.norm_eq_abs] using hCc r c z).trans
      ((le_max_left _ _).trans hp)
  have hau (r c : α) (i j : RIdx n) : Integrable (fun z => ae r c i j z * u z c) (lebesgueC n) :=
    compact_scalar_mul_integrable (lebesgueC n) _ (ha r c i j).continuous hcθ.mul_right _ (hui c)
  have hdau (r c : α) (i j : RIdx n) : Integrable
      (fun z => fderiv ℝ (ae r c i j) z (realModelBasis n j) * u z c) (lebesgueC n) :=
    compact_scalar_mul_integrable (lebesgueC n) _
      (((ha r c i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      (hcθ.mul_right.fderiv_apply ℝ (realModelBasis n j)) _ (hui c)
  have hBu (r c : α) (i : RIdx n) : Integrable (fun z => Be r c i z * u z c) (lebesgueC n) :=
    compact_scalar_mul_integrable (lebesgueC n) _ (hB r c i).continuous hcθ.mul_right _ (hui c)
  have hCu (r c : α) : Integrable (fun z => Ce r c z * u z c) (lebesgueC n) :=
    compact_scalar_mul_integrable (lebesgueC n) _ (hC r c).continuous hcθ.mul_right _ (hui c)
  obtain ⟨ρ, hρ, hcρ, hρ0, hρ1⟩ := exists_model_friedrichs_mollifier n
  obtain ⟨ε, hε, hε1, htε, hεsupport⟩ := exists_mollifier_scales_in_compact_buffer
    (lebesgueC n) ρ hcρ hcχ hΩ hχΩ
  let ρm := fun m => rescaledFriedrichsMollifier ρ (ε m)
  let U := fun m z c => (ρm m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, lebesgueC n] (fun y => u y c)) z
  let V := fun m z r => divergenceMollifierForcing (lebesgueC n) Ce u F0 (ρm m) z r
  let Q := fun m z r i => divergenceMollifierFlux (lebesgueC n) (realModelBasis n) ae Be u F (ρm m) z r i
  have hρm (m : ℕ) : ContDiff ℝ ∞ (ρm m) := rescaledFriedrichsMollifier_contDiff_top ρ (ε m) hρ
  have hcρm (m : ℕ) : HasCompactSupport (ρm m) := rescaledFriedrichsMollifier_compact ρ (hε m).ne' hcρ
  have hU (m : ℕ) (c : α) : ContDiff ℝ ∞ (fun z => U m z c) :=
    (hcρm m).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρm m) (hui c).locallyIntegrable
  have hUK (m : ℕ) (c : α) : tsupport (fun z => U m z c) ⊆ closure Ω :=
    (hεsupport (fun z => u z c) (hs.1 c) m).trans subset_closure
  have hUt (c : α) : Tendsto (fun m => ∫ z, ‖U m z c - u z c‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp (lebesgueC n) ρ (hρ.of_le (by simp))
      hcρ hρ0 hρ1 ε hε hε1 htε (fun z => u z c) (hm.1 c) (hcu c)
  have hVlim (r : α) := divergenceMollifierForcing_L2_tendsto (lebesgueC n) Ce
    (fun r c => (hC r c).continuous) Cc hCc u hm.1 hcu F0 hm.2.1 hcF0
    ρ hρ hcρ hρ0 hρ1 ε hε hε1 htε r
  have hQlim (r : α) (i : RIdx n) := divergenceMollifierFlux_L2_tendsto (lebesgueC n)
    (realModelBasis n) ae ha Kc hKc Ac hAc Be (fun r c i => (hB r c i).continuous) Bc hBc
    u hm.1 hcu F hm.2.2 hcF ρ hρ hcρ hρ0 hρ1 ε hε hε1 htε r i
  have hV (m : ℕ) (r : α) : ContDiff ℝ ∞ (fun z => V m z r) := by
    exact ((hcρm m).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρm m) (hF0i r).locallyIntegrable).add
      (ContDiff.sum (fun c _ => multiplicationMollifierCommutator_contDiff (lebesgueC n)
        (Ce r c) (ρm m) (fun z => u z c) (hC r c) (hρm m) (hcρm m) (hui c) (hCu r c)))
  have hQ (m : ℕ) (r : α) (i : RIdx n) : ContDiff ℝ ∞ (fun z => Q m z r i) := by
    exact (((hcρm m).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρm m) (hFi r i).locallyIntegrable).sub
      (ContDiff.sum (fun c _ => ContDiff.sum (fun j _ => friedrichsCommutatorKernel_raw_contDiff
        (lebesgueC n) (ae r c i j) (ρm m) (fun z => u z c) (ha r c i j) (hρm m) (hcρm m)
        (hui c) (hau r c i j) (realModelBasis n j) (hdau r c i j))))).add
      (ContDiff.sum (fun c _ => multiplicationMollifierCommutator_contDiff (lebesgueC n)
        (Be r c i) (ρm m) (fun z => u z c) (hB r c i) (hρm m) (hcρm m) (hui c) (hBu r c i)))
  have heq (m : ℕ) (z : ComplexVector n) (r : α) : divergenceSystemApply (realModelBasis n) ae Be Ce (U m) z r =
      V m z r + ∑ i, fderiv ℝ (fun y => Q m y r i) z (realModelBasis n i) :=
    divergenceSystemWeakEquation_mollifier_forcing (lebesgueC n) (realModelBasis n) ae Be Ce u F0 F
      ha hB hui hau hdau hBu hCu hF0i hFi hweak (ρm m) (hρm m) (hcρm m) r z
  refine ⟨closure Ω, hcΩ, hΩO, U, hU, hUK, hUt, ?_⟩
  apply DivergenceEnergy.gradient_pair_sq_tendsto_zero (lebesgueC n) (realModelBasis n) ae Be Ce U V Q
    (closure Ω) hcΩ ha hB (fun r c => (hC r c).continuous) hU hUK
    (fun m r => (hV m r).continuous) hQ (fun m r => (hVlim r).1 m) (fun m r i => (hQlim r i).1 m)
    ell b0 c0 hell hb0 hc0 (fun z _ r c i => hboundB z r c i) (fun z _ r c => hboundC z r c)
    hcoercive heq
  · exact DivergenceEnergy.pair_valueSq_tendsto_zero (lebesgueC n) U u
      (fun m c => (hU m c).continuous.memLp_of_hasCompactSupport
        (hcΩ.of_isClosed_subset (isClosed_tsupport _) (hUK m c))) hm.1 hUt
  · exact DivergenceEnergy.pair_valueSq_tendsto_zero (lebesgueC n) V F0
      (fun m r => (hVlim r).1 m) hm.2.1 (fun r => (hVlim r).2)
  · exact DivergenceEnergy.pair_valueSq_tendsto_zero (lebesgueC n)
      (fun m z (q : RIdx n × α) => Q m z q.2 q.1) (fun z (q : RIdx n × α) => F z q.2 q.1)
      (fun m q => (hQlim q.2 q.1).1 m) (fun q => hm.2.2 q.2 q.1) (fun q => (hQlim q.2 q.1).2)

/-- Strong ordinary L² limits of all first derivatives are constructed
for the actual compact chart regularizations of the rough Hodge field. -/
theorem exists_localized_smooth_gradient_limits {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ∃ K : Set (ComplexVector n), IsCompact K ∧ K ⊆ chartTarget x ∧
      ∃ (U : ℕ → ComplexVector n → α → ℝ) (D : ComplexVector n → RIdx n × α → ℝ),
      (∀ m c, ContDiff ℝ ∞ (fun z => U m z c)) ∧
      (∀ m c, tsupport (fun z => U m z c) ⊆ K) ∧
      (∀ c, Tendsto (fun m => ∫ z, ‖U m z c - localizedInput x b χ A z c‖ ^ 2
        ∂lebesgueC n) atTop (𝓝 0)) ∧
      (∀ q, MemLp (fun z => D z q) 2 (lebesgueC n)) ∧
      (∀ q, tsupport (fun z => D z q) ⊆ K) ∧
      ∀ q, Tendsto (fun m => ∫ z, ‖DivergenceEnergy.derivative (realModelBasis n) (U m) z q - D z q‖ ^ 2
        ∂lebesgueC n) atTop (𝓝 0) := by
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  obtain ⟨K, hK, hKO, U, hU, hUK, hUt, hDt⟩ :=
    exists_localized_smooth_gradient_cauchy g μ hμ A hmax x b χ hχ hcχ hχO
  obtain ⟨D, hD, hDK, hDlim⟩ := exists_compact_gradient_limits (lebesgueC n) (realModelBasis n) U hU K hK hUK hDt
  exact ⟨K, hK, hKO, U, D, hU, hUK, hUt, hD, hDK, hDlim⟩

end Yau.LeafProofs.L03.HodgeDivergenceWeak
