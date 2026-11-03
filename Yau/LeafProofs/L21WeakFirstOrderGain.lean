import Yau.LeafProofs.L21GraphApproximation

/-! The first weak gain is obtained from strong graph approximation and
completeness. Every derivative of a rough input is identified by a compact
test identity, with an actual L² representative. -/

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def ComplexWeakDerivative (u g : X n → ℂ) (v : X n) : Prop :=
  ∀ (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ x, u x * (fderiv ℝ ψ x v : ℂ) ∂Yau.lebesgueC n) =
      -(∫ x, g x * (ψ x : ℂ) ∂Yau.lebesgueC n)

theorem exists_compact_complex_gradient_limits
    {O L : Set (X n)} (hL : IsCompact L) (U : ℕ → CompactTest O)
    (hsU : ∀ m, tsupport (U m) ⊆ L)
    (hcauchy : ∀ a : Yau.RIdx n, CauchySeq (fun m =>
      (directional_memLp (U m).property.1 (U m).property.2.1 (Yau.realVec a)).toLp
        (fun x => fderiv ℝ (U m) x (Yau.realVec a)))) :
    ∃ G : X n → Yau.RIdx n → ℂ,
      (∀ a, MemLp (fun x => G x a) 2 (Yau.lebesgueC n)) ∧
      (∀ a, tsupport (fun x => G x a) ⊆ L) ∧
      ∀ a, Tendsto (fun m => ∫ x, ‖fderiv ℝ (U m) x (Yau.realVec a) - G x a‖ ^ 2
        ∂Yau.lebesgueC n) atTop (𝓝 0) := by
  have hex (a : Yau.RIdx n) : ∃ d : Lp ℂ 2 (Yau.lebesgueC n), Tendsto
      (fun m => (directional_memLp (U m).property.1 (U m).property.2.1 (Yau.realVec a)).toLp
        (fun x => fderiv ℝ (U m) x (Yau.realVec a))) atTop (𝓝 d) :=
    cauchySeq_tendsto_of_complete (hcauchy a)
  choose d hd using hex
  let G : X n → Yau.RIdx n → ℂ := fun x a => L.indicator (fun y => d a y) x
  have hG (a : Yau.RIdx n) : MemLp (fun x => G x a) 2 (Yau.lebesgueC n) :=
    (Lp.memLp (d a)).indicator hL.isClosed.measurableSet.nullMeasurableSet
  refine ⟨G, hG, ?_, ?_⟩
  · intro a
    apply closure_minimal ?_ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp only [G, Set.indicator_of_notMem hn])
  · intro a
    have hm (m : ℕ) := directional_memLp (U m).property.1 (U m).property.2.1 (Yau.realVec a)
    have ht := complex_integral_norm_sq_tendsto_of_toLp_tendsto
      (fun m x => fderiv ℝ (U m) x (Yau.realVec a)) (fun x => d a x) hm (Lp.memLp (d a))
      (by simpa only [Lp.toLp_coeFn] using hd a)
    apply squeeze_zero (fun m => integral_nonneg fun x => sq_nonneg _) ?_ ht
    intro m
    apply integral_mono (((hm m).sub (hG a)).integrable_norm_pow (p := 2) (by decide))
      (((hm m).sub (Lp.memLp (d a))).integrable_norm_pow (p := 2) (by decide))
    intro x
    change ‖fderiv ℝ (U m) x (Yau.realVec a) - G x a‖ ^ 2 ≤
      ‖fderiv ℝ (U m) x (Yau.realVec a) - d a x‖ ^ 2
    by_cases hx : x ∈ L
    · simp only [G, Set.indicator_of_mem hx]
      exact le_rfl
    · have hz : fderiv ℝ (U m) x = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hh => hx (hsU m hh))
      simp only [G, Set.indicator_of_notMem hx, hz, _root_.zero_apply, sub_zero,
        norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _

theorem complex_weak_derivative_of_strong_limits {O : Set (X n)}
    (U : ℕ → CompactTest O) (u g : X n → ℂ) (v : X n)
    (hu : MemLp u 2 (Yau.lebesgueC n)) (hg : MemLp g 2 (Yau.lebesgueC n))
    (htU : Tendsto (fun m => ∫ x, ‖U m x - u x‖ ^ 2 ∂Yau.lebesgueC n) atTop (𝓝 0))
    (htg : Tendsto (fun m => ∫ x, ‖fderiv ℝ (U m) x v - g x‖ ^ 2
      ∂Yau.lebesgueC n) atTop (𝓝 0)) : ComplexWeakDerivative u g v := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  intro ψ hψ hcψ
  have hψC : ContDiff ℝ ∞ (fun x => (ψ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hcψC : HasCompactSupport (fun x => (ψ x : ℂ)) := hcψ.comp_left Complex.ofReal_zero
  have hψM : MemLp (fun x => (ψ x : ℂ)) 2 (Yau.lebesgueC n) :=
    hψC.continuous.memLp_of_hasCompactSupport hcψC
  have hdψ : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
    (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdψM : MemLp (fun x => (fderiv ℝ ψ x v : ℂ)) 2 (Yau.lebesgueC n) :=
    Complex.ofRealCLM.comp_memLp' (hdψ.continuous.memLp_of_hasCompactSupport (hcψ.fderiv_apply ℝ v))
  have hUM (m : ℕ) : MemLp (U m) 2 (Yau.lebesgueC n) :=
    (U m).property.1.continuous.memLp_of_hasCompactSupport (U m).property.2.1
  have ht1 := complex_integral_pair_tendsto (fun m => U m) u
    (fun x => (fderiv ℝ ψ x v : ℂ)) hUM hu hdψM htU
  have ht2 := complex_integral_pair_tendsto (fun m x => fderiv ℝ (U m) x v) g
    (fun x => (ψ x : ℂ))
    (fun m => directional_memLp (U m).property.1 (U m).property.2.1 v) hg hψM htg
  have he (m : ℕ) :
      (∫ x, star (fderiv ℝ ψ x v : ℂ) * U m x ∂Yau.lebesgueC n) =
        -(∫ x, star (ψ x : ℂ) * fderiv ℝ (U m) x v ∂Yau.lebesgueC n) := by
    have hh := integral_local_mul_compact_fderiv (O := Set.univ) isOpen_univ
      (((U m).property.1.of_le (by simp)).contDiffOn) (hψC.of_le (by simp)) hcψC (by simp) v
    simpa only [fderiv_ofReal_apply (hψ.differentiable (by simp) _),
      Complex.star_def, Complex.conj_ofReal, mul_comm] using hh
  have heq := tendsto_nhds_unique ht1
    ((ht2.neg).congr' (Filter.Eventually.of_forall fun m => (he m).symm))
  simpa only [Complex.star_def, Complex.conj_ofReal, mul_comm] using heq

theorem compact_weak_first_order_gain {O K : Set (X n)}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (u : X n → ℂ) (w : X n → Fin n → ℂ)
    (hu : MemLp u 2 (Yau.lebesgueC n))
    (hw : ∀ i, MemLp (fun x => w x i) 2 (Yau.lebesgueC n))
    (hsu : tsupport u ⊆ K) (hsw : ∀ i, tsupport (fun x => w x i) ⊆ K)
    (heq : DbarWeakEquation A u w) :
    ∃ (L : Set (X n)) (G : X n → Yau.RIdx n → ℂ), IsCompact L ∧ L ⊆ O ∧
      (∀ a, MemLp (fun x => G x a) 2 (Yau.lebesgueC n)) ∧
      (∀ a, tsupport (fun x => G x a) ⊆ L) ∧
      (∀ a, ComplexWeakDerivative u (fun x => G x a) (Yau.realVec a)) ∧
      (∑ a : Yau.RIdx n, ∫ x, ‖G x a‖ ^ 2 ∂Yau.lebesgueC n) ≤
        16 * ∑ i : Fin n, ∫ x, ‖w x i‖ ^ 2 ∂Yau.lebesgueC n := by
  obtain ⟨L, U, hcL, hLO, hsU, htU, htD⟩ :=
    exists_fixed_support_dbarA_graph_approx hO hK hKO hA u w hu hw hsu hsw heq
  obtain ⟨G, hG, hsG, htG⟩ := exists_compact_complex_gradient_limits hcL U hsU
    (dbarA_graph_convergence_gradient_cauchy hO hA hsmall U w hw (fun i => (htD i).2))
  refine ⟨L, G, hcL, hLO, hG, hsG,
    fun a => complex_weak_derivative_of_strong_limits U u (fun x => G x a)
      (Yau.realVec a) hu (hG a) htU (htG a), ?_⟩
  have ht1 := tendsto_finsetSum Finset.univ (fun a _ =>
    complex_integral_norm_sq_tendsto (fun m x => fderiv ℝ (U m) x (Yau.realVec a))
      (fun x => G x a)
      (fun m => directional_memLp (U m).property.1 (U m).property.2.1 (Yau.realVec a))
      (hG a) (htG a))
  have ht2 := tendsto_finsetSum Finset.univ (fun i _ =>
    complex_integral_norm_sq_tendsto (fun m x => dbarA A i (U m) x) (fun x => w x i)
      (fun m => dbarA_memLp hO hA (U m) i) (hw i) (htD i).2)
  exact le_of_tendsto_of_tendsto ht1 (ht2.const_mul 16)
    (Filter.Eventually.of_forall fun m => first_order_energy_on_compact_tests hO hA hsmall (U m))

end Yau.LeafProofs.L21Aux
