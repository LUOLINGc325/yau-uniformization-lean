import Yau.LeafProofs.L14ComplexCutoff

noncomputable section
open scoped Topology ContDiff Convolution
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

/-- Joint weak complex systems admit a genuine smooth graph approximation
inside one fixed compact subset of their coefficient chart. -/
theorem exists_fixed_support_complex_firstOrder_graph_approx {n : ℕ} {α β ι : Type*}
    [Fintype α] [Fintype ι]
    {O K : Set (ComplexVector n)} (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O)
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) O) (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) O)
    (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (hu : ∀ c, MemLp (fun z => u z c) 2 (lebesgueC n))
    (hw : ∀ r, MemLp (fun z => w z r) 2 (lebesgueC n))
    (hsu : ∀ c, tsupport (fun z => u z c) ⊆ K)
    (hsw : ∀ r, tsupport (fun z => w z r) ⊆ K)
    (hrow : ∀ r (ψ : ComplexVector n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, (ψ z : ℂ) * w z r ∂lebesgueC n) =
        ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z ∂lebesgueC n) :
    ∃ (L : Set (ComplexVector n)) (U : ℕ → ComplexVector n → α → ℂ), IsCompact L ∧ L ⊆ O ∧
      (∀ j c, ContDiff ℝ ∞ (fun z => U j z c) ∧ tsupport (fun z => U j z c) ⊆ L) ∧
      (∀ c q, Tendsto (fun j => ∫ z, ‖complexCoordinateCLM q (U j z c - u z c)‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) ∧
      ∀ r q, (∀ j, MemLp (fun z => complexCoordinateCLM q
        (complexFirstOrderSystemApply v a b (U j) z r - w z r)) 2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖complexCoordinateCLM q
          (complexFirstOrderSystemApply v a b (U j) z r - w z r)‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  letI : (lebesgueC n).IsNegInvariant := by rw [lebesgueC_eq_volume]; infer_instance
  letI : SigmaFinite (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  obtain ⟨η, hη, hcη, hsη, hηrange, hηK⟩ := exists_model_open_cutoff hO hcK hKO
  let A := fun r c i z => (η z : ℂ) * a r c i z
  let B := fun r c z => (η z : ℂ) * b r c z
  have hA (r : β) (c : α) (i : ι) : ContDiff ℝ ∞ (A r c i) ∧ HasCompactSupport (A r c i) := by
    have he := compact_complex_cutoff_properties hO η hη hcη hsη (a r c i) (ha r c i)
    exact ⟨he.1, he.2.1⟩
  have hB (r : β) (c : α) : ContDiff ℝ ∞ (B r c) ∧ HasCompactSupport (B r c) := by
    have he := compact_complex_cutoff_properties hO η hη hcη hsη (b r c) (hb r c)
    exact ⟨he.1, he.2.1⟩
  have hrowAB : ∀ r (ψ : ComplexVector n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, (ψ z : ℂ) * w z r ∂lebesgueC n) =
        ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v A B r c ψ z ∂lebesgueC n :=
    complex_firstOrder_rows_extend_coefficients hO hKO v a b ha u w hsu hrow η hη hηK
  have huR (c : α × Fin 2) : MemLp (fun z => realifiedField u z c) 2 (lebesgueC n) :=
    (complexCoordinateCLM c.2).comp_memLp' (hu c.1)
  have hwR (r : β × Fin 2) : MemLp (fun z => realifiedField w z r) 2 (lebesgueC n) :=
    (complexCoordinateCLM r.2).comp_memLp' (hw r.1)
  have hcuR (c : α × Fin 2) : HasCompactSupport (fun z => realifiedField u z c) := by
    have hc : HasCompactSupport (fun z => u z c.1) := hcK.of_isClosed_subset (isClosed_tsupport _) (hsu c.1)
    exact hc.comp_left (map_zero (complexCoordinateCLM c.2))
  have hcwR (r : β × Fin 2) : HasCompactSupport (fun z => realifiedField w z r) := by
    have hc : HasCompactSupport (fun z => w z r.1) := hcK.of_isClosed_subset (isClosed_tsupport _) (hsw r.1)
    exact hc.comp_left (map_zero (complexCoordinateCLM r.2))
  let f : ContDiffBump (0 : ComplexVector n) := default
  let ρ := f.normed (lebesgueC n)
  let ε := fun j : ℕ => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := one_div_pos.mpr (by positivity)
  have hε1 (j : ℕ) : ε j ≤ 1 := by
    change 1 / ((j : ℝ) + 1) ≤ 1
    apply (div_le_iff₀ (show (0 : ℝ) < (j : ℝ) + 1 by positivity)).mpr
    norm_num
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let UR : ℕ → ComplexVector n → (α × Fin 2) → ℝ := fun j x c =>
    (Yau.LeafProofs.L03.rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, lebesgueC n]
      (fun y => realifiedField u y c)) x
  let U := fun j => complexifyField (UR j)
  have happrox := complex_firstOrder_mollifier_graph_tendsto_of_rows (lebesgueC n) v A B
    (fun r c i => (hA r c i).1) (fun r c i => (hA r c i).2)
    (fun r c => (hB r c).1.continuous) (fun r c => (hB r c).2) u w huR hcuR hwR hcwR
    (complex_firstOrder_rows_components (lebesgueC n) v A B
      (fun r c i => (hA r c i).1) (fun r c => (hB r c).1) u w hu hw hrowAB)
    ρ f.contDiff_normed f.hasCompactSupport_normed f.nonneg_normed f.integral_normed
    ε hε hε1 htε
  change (∀ j c, ContDiff ℝ ∞ (fun x => U j x c) ∧ HasCompactSupport (fun x => U j x c)) ∧ _ at happrox
  have hηu (x : ComplexVector n) (c : α) : (η x : ℂ) * u x c = u x c := by
    by_cases hz : u x c = 0
    · simp only [hz, mul_zero]
    · rw [(hηK x (hsu c (subset_tsupport _ hz))).1, Complex.ofReal_one, one_mul]
  have hηdu (x : ComplexVector n) (c : α) (i : ι) : (fderiv ℝ η x (v i) : ℂ) * u x c = 0 := by
    by_cases hz : u x c = 0
    · simp only [hz, mul_zero]
    · rw [(hηK x (hsu c (subset_tsupport _ hz))).2, ContinuousLinearMap.zero_apply,
        Complex.ofReal_zero, zero_mul]
  have hcomm (r : β) (c : α) (i : ι) :
      Continuous (fun x => (fderiv ℝ η x (v i) : ℂ) * a r c i x) ∧
      HasCompactSupport (fun x => (fderiv ℝ η x (v i) : ℂ) * a r c i x) := by
    have he := compact_complex_cutoff_derivative_properties hO η hη hcη hsη (v i) (a r c i) (ha r c i)
    exact ⟨he.1.continuous, he.2.1⟩
  have hfixed := complex_firstOrder_cutoff_graph_tendsto (lebesgueC n) v a b η hη hcη hηrange u w U
    happrox.1 hu hw happrox.2.1 (fun j r q => (happrox.2.2 r q).1 j)
    (fun r q => (happrox.2.2 r q).2) hηu hηdu hcomm
  exact ⟨tsupport η, fun j x c => (η x : ℂ) * U j x c, hcη, hsη,
    fun j c => ⟨(hfixed.1 j c).1, (hfixed.1 j c).2.2⟩, hfixed.2.1, hfixed.2.2⟩

/-- The same approximation converges in actual complex norm, not merely in
its two real coordinates. -/
theorem exists_fixed_support_complex_firstOrder_graph_approx_norm {n : ℕ} {α β ι : Type*}
    [Fintype α] [Fintype ι]
    {O K : Set (ComplexVector n)} (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O)
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) O) (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) O)
    (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (hu : ∀ c, MemLp (fun z => u z c) 2 (lebesgueC n))
    (hw : ∀ r, MemLp (fun z => w z r) 2 (lebesgueC n))
    (hsu : ∀ c, tsupport (fun z => u z c) ⊆ K)
    (hsw : ∀ r, tsupport (fun z => w z r) ⊆ K)
    (hrow : ∀ r (ψ : ComplexVector n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, (ψ z : ℂ) * w z r ∂lebesgueC n) =
        ∫ z, ∑ c, u z c * complexFormalAdjointTestRow v a b r c ψ z ∂lebesgueC n) :
    ∃ (L : Set (ComplexVector n)) (U : ℕ → ComplexVector n → α → ℂ), IsCompact L ∧ L ⊆ O ∧
      (∀ j c, ContDiff ℝ ∞ (fun z => U j z c) ∧ tsupport (fun z => U j z c) ⊆ L) ∧
      (∀ c, (∀ j, MemLp (fun z => U j z c - u z c) 2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖U j z c - u z c‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) ∧
      ∀ r, (∀ j, MemLp (fun z => complexFirstOrderSystemApply v a b (U j) z r - w z r) 2 (lebesgueC n)) ∧
        Tendsto (fun j => ∫ z, ‖complexFirstOrderSystemApply v a b (U j) z r - w z r‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  obtain ⟨L, U, hcL, hLO, hU, htU, htP⟩ :=
    exists_fixed_support_complex_firstOrder_graph_approx hO hcK hKO v a b ha hb u w hu hw hsu hsw hrow
  refine ⟨L, U, hcL, hLO, hU, ?_, ?_⟩
  · intro c
    apply Yau.LeafProofs.L03.integral_sq_tendsto_zero_of_basis_coordinates
      (lebesgueC n) Complex.basisOneI (fun j z => U j z c - u z c)
    · intro j q
      have hm : MemLp (fun z => U j z c - u z c) 2 (lebesgueC n) :=
        ((hU j c).1.continuous.memLp_of_hasCompactSupport
          (show HasCompactSupport (fun z => U j z c) from
            hcL.of_isClosed_subset (isClosed_tsupport _) (hU j c).2)).sub (hu c)
      exact (complexCoordinateCLM q).comp_memLp' hm
    · exact htU c
  · intro r
    apply Yau.LeafProofs.L03.integral_sq_tendsto_zero_of_basis_coordinates
      (lebesgueC n) Complex.basisOneI
      (fun j z => complexFirstOrderSystemApply v a b (U j) z r - w z r)
    · intro j q
      exact (htP r q).1 j
    · exact fun q => (htP r q).2

end Yau.LeafProofs.L14Aux
