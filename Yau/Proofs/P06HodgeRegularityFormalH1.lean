import Yau.Proofs.P06HodgeRegularityEnergy
import Yau.Proofs.P06HodgeRegularityScalarEnergy
import Yau.LeafProofs.L03DivergenceResidualL2
import Yau.LeafProofs.L03MollifierSupport

/-! Generic finite formal value-plus-flux source H¹ gain. The kernel,
scales, exact smooth equation and strong source limits are internal. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Convolution

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]

theorem regularityCompact_scalar_mul_integrable
    (a : E → ℝ) (ha : Continuous a) (hca : HasCompactSupport a)
    (u : E → ℝ) (hu : Integrable u ν) : Integrable (fun z => a z * u z) ν := by
  obtain ⟨d, hd⟩ := hca.exists_bound_of_continuous ha
  exact (hu.bdd_smul d ha.aestronglyMeasurable (Eventually.of_forall hd)).congr
    (Eventually.of_forall fun _ => rfl)

theorem regularityFormalSource_compact_h1
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (B : α → α → ι → E → ℝ) (C : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j)) (hca : ∀ r c i j, HasCompactSupport (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i)) (hcB : ∀ r c i, HasCompactSupport (B r c i))
    (hC : ∀ r c, ContDiff ℝ ∞ (C r c)) (hcC : ∀ r c, HasCompactSupport (C r c))
    (u F0 : E → α → ℝ) (F : E → α → ι → ℝ)
    (hu : ∀ c, MemLp (fun z => u z c) 2 ν) (hF0 : ∀ r, MemLp (fun z => F0 z r) 2 ν)
    (hF : ∀ r i, MemLp (fun z => F z r i) 2 ν)
    (χ : E → ℝ) (hcχ : HasCompactSupport χ)
    (huχ : ∀ c, tsupport (fun z => u z c) ⊆ tsupport χ)
    (hF0χ : ∀ r, tsupport (fun z => F0 z r) ⊆ tsupport χ)
    (hFχ : ∀ r i, tsupport (fun z => F z r i) ⊆ tsupport χ)
    (hweak : divergenceSystemWeakEquation ν v a B C u F0 F)
    (O : Set E) (hO : IsOpen O) (hcO : IsCompact (closure O)) (hχO : tsupport χ ⊆ O)
    (ell : ℝ) (hell : 0 < ell)
    (hcoercive : ∀ z ∈ closure O, ∀ ξ : ι × α → ℝ,
      ell * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ c, ∑ i, ∑ j, a r c i j z * ξ (j,c) * ξ (i,r)) :
    ∃ (U : ℕ → E → α → ℝ) (D : E → ι × α → ℝ),
      (∀ m c, ContDiff ℝ ∞ (fun z => U m z c)) ∧
      (∀ m c, tsupport (fun z => U m z c) ⊆ closure O) ∧
      (∀ c, Tendsto (fun m => ∫ z, ‖U m z c - u z c‖^2 ∂ν) atTop (𝓝 0)) ∧
      (∀ p, MemLp (fun z => D z p) 2 ν) ∧
      (∀ p, tsupport (fun z => D z p) ⊆ closure O) ∧
      (∀ p, Tendsto (fun m => ∫ z,
        ‖DivergenceEnergy.derivative v (U m) z p - D z p‖^2 ∂ν) atTop (𝓝 0)) ∧
      ∀ i r, regularityWeakDeriv ν Set.univ (v i) (fun z => u z r) (fun z => D z (i,r)) := by
  classical
  have hcu (c : α) : HasCompactSupport (fun z => u z c) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (huχ c)
  have hcf0 (r : α) : HasCompactSupport (fun z => F0 z r) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (hF0χ r)
  have hcf (r : α) (i : ι) : HasCompactSupport (fun z => F z r i) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (hFχ r i)
  have hui (c : α) := memLp_two_compact_integrable ν (fun z => u z c) (hu c) (hcu c)
  have hF0i (r : α) := memLp_two_compact_integrable ν (fun z => F0 z r) (hF0 r) (hcf0 r)
  have hFi (r : α) (i : ι) := memLp_two_compact_integrable ν (fun z => F z r i) (hF r i) (hcf r i)
  choose Ac Kc hAc hKc using fun r c i j => compact_contDiff_coefficient_bounds
    (a r c i j) (ha r c i j) (hca r c i j)
  choose Bc hBc using fun r c i => (hB r c i).continuous.bounded_above_of_compact_support (hcB r c i)
  choose Cc hCc using fun r c => (hC r c).continuous.bounded_above_of_compact_support (hcC r c)
  let b0 : ℝ := ∑ p : α × α × ι, max (Bc p.1 p.2.1 p.2.2) 0
  let c0 : ℝ := ∑ p : α × α, max (Cc p.1 p.2) 0
  have hb0 : 0 ≤ b0 := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hboundB (z : E) (r c : α) (i : ι) : |B r c i z| ≤ b0 := by
    have hp : max (Bc r c i) 0 ≤ b0 := Finset.single_le_sum
      (f := fun p : α × α × ι => max (Bc p.1 p.2.1 p.2.2) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ (r,c,i))
    exact (show |B r c i z| ≤ Bc r c i by simpa only [Real.norm_eq_abs] using hBc r c i z).trans
      ((le_max_left _ _).trans hp)
  have hboundC (z : E) (r c : α) : |C r c z| ≤ c0 := by
    have hp : max (Cc r c) 0 ≤ c0 := Finset.single_le_sum
      (f := fun p : α × α => max (Cc p.1 p.2) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ (r,c))
    exact (show |C r c z| ≤ Cc r c by simpa only [Real.norm_eq_abs] using hCc r c z).trans
      ((le_max_left _ _).trans hp)
  have hau (r c : α) (i j : ι) : Integrable (fun z => a r c i j z * u z c) ν :=
    regularityCompact_scalar_mul_integrable ν _ (ha r c i j).continuous (hca r c i j) _ (hui c)
  have hdau (r c : α) (i j : ι) : Integrable (fun z => fderiv ℝ (a r c i j) z (v j) * u z c) ν :=
    regularityCompact_scalar_mul_integrable ν _
      ((regularityDirection_contDiff (ha r c i j) (v j)).continuous)
      ((hca r c i j).fderiv_apply ℝ (v j)) _ (hui c)
  have hBu (r c : α) (i : ι) : Integrable (fun z => B r c i z * u z c) ν :=
    regularityCompact_scalar_mul_integrable ν _ (hB r c i).continuous (hcB r c i) _ (hui c)
  have hCu (r c : α) : Integrable (fun z => C r c z * u z c) ν :=
    regularityCompact_scalar_mul_integrable ν _ (hC r c).continuous (hcC r c) _ (hui c)
  let bump : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
  let ρ := bump.normed ν
  have hρ : ContDiff ℝ ∞ ρ := bump.contDiff_normed
  have hcρ : HasCompactSupport ρ := bump.hasCompactSupport_normed
  have hρ0 : ∀ z, 0 ≤ ρ z := bump.nonneg_normed
  have hρ1 : (∫ z, ρ z ∂ν) = 1 := bump.integral_normed
  obtain ⟨ε, hε, hε1, htε, hsupp⟩ := exists_mollifier_scales_in_compact_buffer ν ρ hcρ hcχ hO hχO
  let ρm := fun m => rescaledFriedrichsMollifier ρ (ε m)
  let U := fun m z c => (ρm m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun z => u z c)) z
  let V := fun m z r => divergenceMollifierForcing ν C u F0 (ρm m) z r
  let Q := fun m z r i => divergenceMollifierFlux ν v a B u F (ρm m) z r i
  have hρm (m : ℕ) : ContDiff ℝ ∞ (ρm m) := rescaledFriedrichsMollifier_contDiff_top ρ (ε m) hρ
  have hcρm (m : ℕ) : HasCompactSupport (ρm m) := rescaledFriedrichsMollifier_compact ρ (hε m).ne' hcρ
  have hU (m : ℕ) (c : α) : ContDiff ℝ ∞ (fun z => U m z c) :=
    (hcρm m).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρm m) (hui c).locallyIntegrable
  have hUK (m : ℕ) (c : α) : tsupport (fun z => U m z c) ⊆ closure O :=
    (hsupp (fun z => u z c) (huχ c) m).trans subset_closure
  have hUt (c : α) : Tendsto (fun m => ∫ z, ‖U m z c - u z c‖^2 ∂ν) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp ν ρ (hρ.of_le (by simp)) hcρ hρ0 hρ1
      ε hε hε1 htε (fun z => u z c) (hu c) (hcu c)
  have hVlim (r : α) := divergenceMollifierForcing_L2_tendsto ν C
    (fun r c => (hC r c).continuous) Cc hCc u hu hcu F0 hF0 hcf0 ρ hρ hcρ hρ0 hρ1 ε hε hε1 htε r
  have hQlim (r : α) (i : ι) := divergenceMollifierFlux_L2_tendsto ν v a ha Kc hKc Ac hAc
    B (fun r c i => (hB r c i).continuous) Bc hBc u hu hcu F hF hcf ρ hρ hcρ hρ0 hρ1 ε hε hε1 htε r i
  have hV (m : ℕ) (r : α) : ContDiff ℝ ∞ (fun z => V m z r) :=
    ((hcρm m).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρm m) (hF0i r).locallyIntegrable).add
      (ContDiff.sum fun c _ => multiplicationMollifierCommutator_contDiff ν
        (C r c) (ρm m) (fun z => u z c) (hC r c) (hρm m) (hcρm m) (hui c) (hCu r c))
  have hQ (m : ℕ) (r : α) (i : ι) : ContDiff ℝ ∞ (fun z => Q m z r i) :=
    (((hcρm m).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρm m) (hFi r i).locallyIntegrable).sub
      (ContDiff.sum fun c _ => ContDiff.sum fun j _ => friedrichsCommutatorKernel_raw_contDiff ν
        (a r c i j) (ρm m) (fun z => u z c) (ha r c i j) (hρm m) (hcρm m)
        (hui c) (hau r c i j) (v j) (hdau r c i j))).add
      (ContDiff.sum fun c _ => multiplicationMollifierCommutator_contDiff ν
        (B r c i) (ρm m) (fun z => u z c) (hB r c i) (hρm m) (hcρm m) (hui c) (hBu r c i))
  have heq (m : ℕ) (z : E) (r : α) : divergenceSystemApply v a B C (U m) z r =
      V m z r + ∑ i, fderiv ℝ (fun y => Q m y r i) z (v i) :=
    divergenceSystemWeakEquation_mollifier_forcing ν v a B C u F0 F
      ha hB hui hau hdau hBu hCu hF0i hFi hweak (ρm m) (hρm m) (hcρm m) r z
  obtain ⟨D, hD, hDK, hDt, hDW⟩ := regularitySystem_exists_weak_gradient ν v a B C U V Q u F0 F
    (closure O) hcO ha hB (fun r c => (hC r c).continuous) hU hUK
    (fun m r => (hV m r).continuous) hQ (fun m r => (hVlim r).1 m)
    (fun m r i => (hQlim r i).1 m) hu hF0 hF ell b0 c0 hell hb0 hc0
    (fun z _ r c i => hboundB z r c i) (fun z _ r c => hboundC z r c) hcoercive heq
    hUt (fun r => (hVlim r).2) (fun r i => (hQlim r i).2)
  exact ⟨U, D, hU, hUK, hUt, hD, hDK, hDt, hDW⟩

end Yau.NodeProofs.P06Aux
