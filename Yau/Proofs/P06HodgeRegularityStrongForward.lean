import Yau.Proofs.P06HodgeRegularitySmoothForward

/-! Passing the actual forward PDE through simultaneous strong L² limits
of its two entries. Derivatives occur only on fixed compact smooth tests. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α] [DecidableEq α]
    (ν : Measure E) [ν.IsAddHaarMeasure]

theorem regularityForwardWeak_of_strong_smooth
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (Us Ws : ℕ → E → α → ℝ) (U W : E → α → ℝ)
    (hUs : ∀ m c, ContDiff ℝ ∞ (fun z => Us m z c))
    (hUsL : ∀ m c, MemLp (fun z => Us m z c) 2 ν) (hWsL : ∀ m c, MemLp (fun z => Ws m z c) 2 ν)
    (hU : ∀ c, MemLp (fun z => U z c) 2 ν) (hW : ∀ c, MemLp (fun z => W z c) 2 ν)
    (hUt : ∀ c, Tendsto (fun m => ∫ z, ‖Us m z c - U z c‖^2 ∂ν) atTop (𝓝 0))
    (hWt : ∀ c, Tendsto (fun m => ∫ z, ‖Ws m z c - W z c‖^2 ∂ν) atTop (𝓝 0))
    {O : Set E}
    (heq : ∀ m z, z ∈ O → ∀ r,
      hodgeForwardPrincipal v (regularityScalarSystemA q) e1 e0 (Us m) z r = Ws m z r) :
    regularityForwardWeak ν O v q e1 e0 U W := by
  classical
  have ha := regularityScalarSystemA_contDiff (α := α) q hq
  intro r φ hφ
  rw [regularityForwardTranspose_integral_restrict ν v _ e1 e0 ha he1 he0 hφ U r,
    regularityForwardSource_integral_restrict ν hφ (fun z => W z r)]
  let T (c : α) (z : E) := regularityForwardTranspose v (regularityScalarSystemA q) e1 e0 φ z r c
  have hTL c : MemLp (T c) 2 ν :=
    (regularityForwardTranspose_test v _ e1 e0 ha he1 he0 hφ r c).1.continuous.memLp_of_hasCompactSupport
      (regularityForwardTranspose_test v _ e1 e0 ha he1 he0 hφ r c).2.1
  have hleft := tendsto_finset_sum Finset.univ (fun c _ => regularity_integral_pairing_tendsto ν
    (fun m z => Us m z c) (fun z => U z c) (T c) (fun m => hUsL m c) (hU c) (hTL c) (hUt c))
  have hright := regularity_integral_pairing_tendsto ν (fun m z => Ws m z r) (fun z => W z r) φ
    (fun m => hWsL m r) (hW r) (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1) (hWt r)
  have hexpand (V : E → α → ℝ) (hV : ∀ c, MemLp (fun z => V z c) 2 ν) :
      (∫ z, ∑ c, T c z * V z c ∂ν) = ∑ c, ∫ z, V z c * T c z ∂ν := by
    have hi (c : α) : Integrable (fun z => T c z * V z c) ν := (hTL c).integrable_mul (hV c)
    rw [integral_finsetSum Finset.univ (fun c _ => hi c)]
    apply Finset.sum_congr rfl
    intro c _
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  have hseq (m : ℕ) : (∑ c, ∫ z, Us m z c * T c z ∂ν) = ∫ z, Ws m z r * φ z ∂ν := by
    rw [← hexpand (Us m) (hUsL m)]
    change (∫ z, ∑ c, regularityForwardTranspose v _ e1 e0 φ z r c * Us m z c ∂ν) = _
    rw [regularitySmoothTranspose_principal ν v _ e1 e0 ha he1 he0 (Us m) (hUs m) (hUsL m) hφ.1 hφ.2.1]
    apply integral_congr_ae (Eventually.of_forall _)
    intro z
    by_cases hz : z ∈ O
    · rw [heq m z hz r,mul_comm]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφ.2.2 h)),zero_mul,mul_zero]
  rw [hexpand U hU]
  have heqW : (∫ z, φ z * W z r ∂ν) = ∫ z, W z r * φ z ∂ν :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [heqW]
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun m => (hseq m).symm))

end Yau.NodeProofs.P06Aux
