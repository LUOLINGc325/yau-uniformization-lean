import Yau.LeafProofs.L03DivergenceMollifier
import Yau.LeafProofs.L03ChartApprox

open MeasureTheory Filter
open scoped Topology ContDiff Convolution

noncomputable section

namespace Yau.LeafProofs.L03

/-- Finite strong L² errors can be added to a convergent rough sequence. -/
theorem strongL2_tendsto_add_finite_errors {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (U : ℕ → E → ℝ) (f : E → ℝ)
    (hU : ∀ j, MemLp (U j) 2 ν) (hf : MemLp f 2 ν)
    (htU : Tendsto (fun j => ∫ x, ‖U j x - f x‖ ^ 2 ∂ν) atTop (𝓝 0))
    (R : ℕ → E → ι → ℝ) (hR : ∀ j i, MemLp (fun x => R j x i) 2 ν)
    (htR : ∀ i, Tendsto (fun j => ∫ x, ‖R j x i‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    (∀ j, MemLp (fun x => U j x + ∑ i, R j x i) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖U j x + ∑ i, R j x i - f x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  let T : ℕ → E → Option ι → ℝ := fun j x i => match i with
    | none => U j x - f x
    | some i => R j x i
  have hT (j : ℕ) (i : Option ι) : MemLp (fun x => T j x i) 2 ν := by
    cases i with
    | none => exact (hU j).sub hf
    | some i => exact hR j i
  have htT (i : Option ι) : Tendsto (fun j => ∫ x, ‖T j x i‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    cases i with
    | none => exact htU
    | some i => exact htR i
  have hsum := integral_sq_tendsto_zero_fintype_sum ν T hT htT
  refine ⟨fun j => (hU j).add (memLp_finsetSum (f := fun i x => R j x i) Finset.univ
    (fun i _ => hR j i)), ?_⟩
  have heq (j : ℕ) (x : E) : U j x + ∑ i, R j x i - f x = ∑ i, T j x i := by
    simp only [Fintype.sum_option, T]
    ring
  simpa only [heq] using hsum.2

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]

theorem rescaledMollifier_memLp_two (ρ : E → ℝ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρ1 : (∫ z, ρ z ∂ν) = 1) (f : E → ℝ) (hf : MemLp f 2 ν)
    (hcf : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    MemLp (rescaledFriedrichsMollifier ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) 2 ν := by
  have hp0 (z : E) : 0 ≤ rescaledFriedrichsMollifier ρ ε z :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (hρ0 _)
  have hp1 : (∫ z, rescaledFriedrichsMollifier ρ ε z ∂ν) = 1 := by
    rw [rescaledFriedrichsMollifier_integral ν ρ hε, hρ1]
  exact (probability_convolution_L2_bound ν _ hp0 hp1 f (memLp_two_compact_integrable ν f hf hcf)
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)).1

/-- The already proved first-order Friedrichs error is both an actual
L² field at every scale and strongly zero in L², for raw compact inputs. -/
theorem friedrichsCommutatorKernel_raw_L2_tendsto (a ρ : E → ℝ)
    (ha : ContDiff ℝ ∞ a) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (K : NNReal) (haK : LipschitzWith K a) (A : ℝ) (haA : ∀ x, ‖a x‖ ≤ A)
    (f : E → ℝ) (hf : MemLp f 2 ν) (hcf : HasCompactSupport f) (v : E)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) :
    let R := fun j x => ∫ y,
      friedrichsCommutatorKernel a (rescaledFriedrichsMollifier ρ (ε j)) v x y * f y ∂ν
    (∀ j, MemLp (R j) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖R j x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  dsimp only
  have hfi := memLp_two_compact_integrable ν f hf hcf
  have hfa : Integrable (fun y => a y * f y) ν :=
    (hfi.bdd_smul A ha.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall haA)).congr (Filter.Eventually.of_forall fun _ => rfl)
  have hdac : Continuous (fun y => fderiv ℝ a y v) :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdaBound (y : E) : ‖fderiv ℝ a y v‖ ≤ (K : ℝ) * ‖v‖ :=
    ((fderiv ℝ a y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ haK) (norm_nonneg v))
  have hfda : Integrable (fun y => fderiv ℝ a y v * f y) ν :=
    (hfi.bdd_smul ((K : ℝ) * ‖v‖) hdac.aestronglyMeasurable
      (Filter.Eventually.of_forall hdaBound)).congr (Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨?_, ?_⟩
  · intro j
    have hsm := friedrichsCommutatorKernel_raw_contDiff ν a (rescaledFriedrichsMollifier ρ (ε j)) f ha
      (rescaledFriedrichsMollifier_contDiff_top ρ (ε j) hρ)
      (rescaledFriedrichsMollifier_compact ρ (hε j).ne' hcρ) hfi hfa v hfda
    have hi := (friedrichs_commutator_uniform_L2_bound ν a ρ (ha.of_le (by simp))
      (hρ.of_le (by simp)) hcρ K haK v f hfi
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)).2 (ε j) (hε j)
    apply (memLp_two_iff_integrable_sq_norm hsm.continuous.aestronglyMeasurable).mpr
    simpa only [smul_eq_mul] using hi.1
  · simpa only [smul_eq_mul] using friedrichs_commutator_L2_tendsto_of_memLp ν a ρ
      (ha.of_le (by simp)) (hρ.of_le (by simp)) hcρ hρ0 hρ1 K haK A haA f hf hcf v ε hε hε1 ht

def divergenceMollifierForcing {α β : Type*} [Fintype α]
    (C : β → α → E → ℝ) (u : E → α → ℝ) (F0 : E → β → ℝ)
    (ρ : E → ℝ) (x : E) (r : β) : ℝ :=
  (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F0 y r)) x +
    ∑ c, multiplicationMollifierCommutator ν (C r c) ρ (fun y => u y c) x

def divergenceMollifierFlux {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → ι → E → ℝ) (B : β → α → ι → E → ℝ)
    (u : E → α → ℝ) (F : E → β → ι → ℝ)
    (ρ : E → ℝ) (x : E) (r : β) (i : ι) : ℝ :=
  (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) x -
    (∑ c, ∑ j, ∫ y, friedrichsCommutatorKernel (a r c i j) ρ (v j) x y * u y c ∂ν) +
    ∑ c, multiplicationMollifierCommutator ν (B r c i) ρ (fun y => u y c) x

theorem directional_fderiv_fintype_sum {ι : Type*} [Fintype ι]
    (f : ι → E → ℝ) (hf : ∀ i, DifferentiableAt ℝ (f i) x) (v : E) :
    fderiv ℝ (fun z => ∑ i, f i z) x v = ∑ i, fderiv ℝ (f i) x v := by
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp only [ContinuousLinearMap.sum_apply]

/-- The exact mollified PDE has the ordinary divergence forcing form
needed for the compact-buffer energy estimate. Both forcing fields are
the explicitly defined fields whose strong L² limits are proved below. -/
theorem divergenceSystemWeakEquation_mollifier_forcing {α β ι : Type*}
    [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (B : β → α → ι → E → ℝ) (C : β → α → E → ℝ)
    (u : E → α → ℝ) (F0 : E → β → ℝ) (F : E → β → ι → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hu : ∀ c, Integrable (fun y => u y c) ν)
    (hau : ∀ r c i j, Integrable (fun y => a r c i j y * u y c) ν)
    (hdau : ∀ r c i j, Integrable (fun y => fderiv ℝ (a r c i j) y (v j) * u y c) ν)
    (hBu : ∀ r c i, Integrable (fun y => B r c i y * u y c) ν)
    (hCu : ∀ r c, Integrable (fun y => C r c y * u y c) ν)
    (hF0 : ∀ r, Integrable (fun y => F0 y r) ν)
    (hF : ∀ r i, Integrable (fun y => F y r i) ν)
    (hweak : divergenceSystemWeakEquation ν v a B C u F0 F)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (r : β) (x : E) :
    divergenceSystemApply v a B C
        (fun z c => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => u y c)) z) x r =
      divergenceMollifierForcing ν C u F0 ρ x r +
        ∑ i, fderiv ℝ (fun z => divergenceMollifierFlux ν v a B u F ρ z r i) x (v i) := by
  classical
  let R : α → ι → ι → E → ℝ := fun c i j z =>
    ∫ y, friedrichsCommutatorKernel (a r c i j) ρ (v j) z y * u y c ∂ν
  let Q : α → ι → E → ℝ := fun c i => multiplicationMollifierCommutator ν (B r c i) ρ (fun y => u y c)
  have hRs (c : α) (i j : ι) : ContDiff ℝ ∞ (R c i j) :=
    friedrichsCommutatorKernel_raw_contDiff ν (a r c i j) ρ (fun y => u y c)
      (ha r c i j) hρ hcρ (hu c) (hau r c i j) (v j) (hdau r c i j)
  have hQs (c : α) (i : ι) : ContDiff ℝ ∞ (Q c i) :=
    multiplicationMollifierCommutator_contDiff ν (B r c i) ρ (fun y => u y c)
      (hB r c i) hρ hcρ (hu c) (hBu r c i)
  have hG (i : ι) : fderiv ℝ (fun z => divergenceMollifierFlux ν v a B u F ρ z r i) x (v i) =
      fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) x (v i) -
        (∑ c, ∑ j, fderiv ℝ (R c i j) x (v i)) + ∑ c, fderiv ℝ (Q c i) x (v i) := by
    have hJ : ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) :=
      hcρ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ (hF r i).locallyIntegrable
    have hsumR : ContDiff ℝ ∞ (fun z => ∑ c, ∑ j, R c i j z) :=
      ContDiff.sum (fun c _ => ContDiff.sum (fun j _ => hRs c i j))
    have hsumQ : ContDiff ℝ ∞ (fun z => ∑ c, Q c i z) := ContDiff.sum (fun c _ => hQs c i)
    change fderiv ℝ (fun z =>
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) z -
        (∑ c, ∑ j, R c i j z) + ∑ c, Q c i z) x (v i) = _
    rw [fderiv_fun_add ((hJ.sub hsumR).differentiable (by simp) x) (hsumQ.differentiable (by simp) x),
      fderiv_fun_sub (hJ.differentiable (by simp) x) (hsumR.differentiable (by simp) x)]
    simp only [add_apply, sub_apply]
    rw [directional_fderiv_fintype_sum (fun c z => ∑ j, R c i j z)
      (fun c => (ContDiff.sum (fun j _ => hRs c i j)).differentiable (by simp) x),
      directional_fderiv_fintype_sum (fun c z => Q c i z) (fun c => (hQs c i).differentiable (by simp) x)]
    congr 2
    apply Finset.sum_congr rfl
    intro c _
    exact directional_fderiv_fintype_sum (R c i) (fun j => (hRs c i j).differentiable (by simp) x) (v i)
  have hm := divergenceSystemWeakEquation_mollifier_residual ν v a B C u F0 F ha hB hu hau hdau hBu hCu hF0 hF hweak ρ hρ hcρ r x
  change _ = _ + _ + _ - (∑ c, ∑ i, ∑ j, fderiv ℝ (R c i j) x (v i)) +
    ∑ c, ∑ i, fderiv ℝ (Q c i) x (v i) at hm
  rw [hm]
  unfold divergenceMollifierForcing
  simp_rw [hG]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hRcomm : (∑ i, ∑ c, ∑ j, fderiv ℝ (R c i j) x (v i)) =
      ∑ c, ∑ i, ∑ j, fderiv ℝ (R c i j) x (v i) := Finset.sum_comm
  have hQcomm : (∑ i, ∑ c, fderiv ℝ (Q c i) x (v i)) =
      ∑ c, ∑ i, fderiv ℝ (Q c i) x (v i) := Finset.sum_comm
  rw [hRcomm, hQcomm]
  ring

/-- The zeroth-order residual data converge strongly to the original
raw L² forcing; no second derivative estimate is used. -/
theorem divergenceMollifierForcing_L2_tendsto {α β : Type*} [Fintype α]
    (C : β → α → E → ℝ) (hC : ∀ r c, Continuous (C r c))
    (C0 : β → α → ℝ) (hC0 : ∀ r c x, ‖C r c x‖ ≤ C0 r c)
    (u : E → α → ℝ) (hu : ∀ c, MemLp (fun y => u y c) 2 ν)
    (hcu : ∀ c, HasCompactSupport (fun y => u y c))
    (F0 : E → β → ℝ) (hF0 : ∀ r, MemLp (fun y => F0 y r) 2 ν)
    (hcF0 : ∀ r, HasCompactSupport (fun y => F0 y r))
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) (r : β) :
    (∀ j, MemLp (fun x => divergenceMollifierForcing ν C u F0
      (rescaledFriedrichsMollifier ρ (ε j)) x r) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖divergenceMollifierForcing ν C u F0
        (rescaledFriedrichsMollifier ρ (ε j)) x r - F0 x r‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  have hM (c : α) := zeroth_order_commutator_L2_tendsto ν (C r c) ρ (hC r c) (C0 r c) (hC0 r c)
    (hρ.of_le (by simp)) hcρ hρ0 hρ1 ε hε hε1 ht (fun y => u y c) (hu c) (hcu c)
  exact strongL2_tendsto_add_finite_errors ν
    (fun j => rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F0 y r))
    (fun y => F0 y r)
    (fun j => rescaledMollifier_memLp_two ν ρ hρ0 hρ1 _ (hF0 r) (hcF0 r) (hε j)) (hF0 r)
    (rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp ν ρ (hρ.of_le (by simp)) hcρ hρ0 hρ1
      ε hε hε1 ht (fun y => F0 y r) (hF0 r) (hcF0 r))
    (fun j x c => multiplicationMollifierCommutator ν (C r c)
      (rescaledFriedrichsMollifier ρ (ε j)) (fun y => u y c) x)
    (fun j c => (hM c).1 j) (fun c => (hM c).2)

/-- The principal residual fluxes also converge strongly to the original
L² flux data. The only errors are the verified first-order kernels. -/
theorem divergenceMollifierFlux_L2_tendsto {α β ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (K : β → α → ι → ι → NNReal) (haK : ∀ r c i j, LipschitzWith (K r c i j) (a r c i j))
    (A0 : β → α → ι → ι → ℝ) (haA : ∀ r c i j x, ‖a r c i j x‖ ≤ A0 r c i j)
    (B : β → α → ι → E → ℝ) (hB : ∀ r c i, Continuous (B r c i))
    (B0 : β → α → ι → ℝ) (hB0 : ∀ r c i x, ‖B r c i x‖ ≤ B0 r c i)
    (u : E → α → ℝ) (hu : ∀ c, MemLp (fun y => u y c) 2 ν)
    (hcu : ∀ c, HasCompactSupport (fun y => u y c))
    (F : E → β → ι → ℝ) (hF : ∀ r i, MemLp (fun y => F y r i) 2 ν)
    (hcF : ∀ r i, HasCompactSupport (fun y => F y r i))
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) (r : β) (i : ι) :
    (∀ j, MemLp (fun x => divergenceMollifierFlux ν v a B u F
      (rescaledFriedrichsMollifier ρ (ε j)) x r i) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖divergenceMollifierFlux ν v a B u F
        (rescaledFriedrichsMollifier ρ (ε j)) x r i - F x r i‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  let γ := (α × ι) ⊕ α
  let R : ℕ → E → γ → ℝ := fun m x s => match s with
    | .inl (c, j) => -(∫ y, friedrichsCommutatorKernel (a r c i j)
        (rescaledFriedrichsMollifier ρ (ε m)) (v j) x y * u y c ∂ν)
    | .inr c => multiplicationMollifierCommutator ν (B r c i)
        (rescaledFriedrichsMollifier ρ (ε m)) (fun y => u y c) x
  have hR (c : α) (j : ι) := friedrichsCommutatorKernel_raw_L2_tendsto ν (a r c i j) ρ
    (ha r c i j) hρ hcρ hρ0 hρ1 (K r c i j) (haK r c i j) (A0 r c i j) (haA r c i j)
    (fun y => u y c) (hu c) (hcu c) (v j) ε hε hε1 ht
  have hM (c : α) := zeroth_order_commutator_L2_tendsto ν (B r c i) ρ (hB r c i) (B0 r c i) (hB0 r c i)
    (hρ.of_le (by simp)) hcρ hρ0 hρ1 ε hε hε1 ht (fun y => u y c) (hu c) (hcu c)
  have hRm (m : ℕ) (s : γ) : MemLp (fun x => R m x s) 2 ν := by
    rcases s with ⟨c, j⟩ | c
    · exact ((hR c j).1 m).neg
    · exact (hM c).1 m
  have htR (s : γ) : Tendsto (fun m => ∫ x, ‖R m x s‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    rcases s with ⟨c, j⟩ | c
    · simpa only [R, norm_neg] using (hR c j).2
    · exact (hM c).2
  have hs := strongL2_tendsto_add_finite_errors ν
    (fun m => rescaledFriedrichsMollifier ρ (ε m) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i))
    (fun y => F y r i)
    (fun m => rescaledMollifier_memLp_two ν ρ hρ0 hρ1 _ (hF r i) (hcF r i) (hε m)) (hF r i)
    (rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp ν ρ (hρ.of_le (by simp)) hcρ hρ0 hρ1
      ε hε hε1 ht (fun y => F y r i) (hF r i) (hcF r i)) R hRm htR
  have heq (m : ℕ) (x : E) : divergenceMollifierFlux ν v a B u F
      (rescaledFriedrichsMollifier ρ (ε m)) x r i =
      (rescaledFriedrichsMollifier ρ (ε m) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => F y r i)) x +
        ∑ s, R m x s := by
    simp only [divergenceMollifierFlux, γ, Fintype.sum_sum_type, Fintype.sum_prod_type, R,
      Finset.sum_neg_distrib]
    ring
  simpa only [heq] using hs

end Euclidean

end Yau.LeafProofs.L03
