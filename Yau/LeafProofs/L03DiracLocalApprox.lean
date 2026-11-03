import Yau.LeafProofs.L03DiracLocal

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

set_option maxHeartbeats 2000000 in
/-- An exact extended weak system produces smooth compact model graph
approximants, without assuming a maximal graph for its raw inputs. -/
theorem dirac_exists_compact_chart_model_approximants_of_extended_weak_system {α : Type*}
    [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A)
    (hW : OperatorCandidates.GradedL2 g.form μ W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j))
    (hcW : ∀ j, CompactlySupportedRealForm (W j)) (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (hWx : ∀ j, closure {y | W j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (b : Basis α ℝ (modelGradedFiber n))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (hχrange : ∀ z, χ z ∈ Set.Icc (0 : ℝ) 1)
    (hχK : ∀ z ∈ tsupport (modelGradedChartPullbackZero A x) ∪
        tsupport (modelGradedChartPullbackZero W x), χ z = 1 ∧ fderiv ℝ χ z = 0)
    (hAe : ∀ r c i, ContDiff ℝ ∞
      (fun z => χ z * diracScalarDerivativeCoefficient g.form x b r c i z))
    (hBe : ∀ r c, ContDiff ℝ ∞
      (fun z => χ z * diracScalarValueCoefficient g.form x b r c z))
    (hweak : firstOrderSystemWeakEquation (lebesgueC n) (realModelBasis n)
      (fun r c i z => χ z * diracScalarDerivativeCoefficient g.form x b r c i z)
      (fun r c z => χ z * diracScalarValueCoefficient g.form x b r c z)
      (fun z c => b.repr (modelGradedChartPullbackZero A x z) c)
      (fun z r => b.repr (modelGradedChartPullbackZero W x z) r)) :
    ∃ K : Set (ComplexVector n), IsCompact K ∧ K ⊆ chartTarget x ∧
      tsupport (modelGradedChartPullbackZero A x) ⊆ K ∧
      tsupport (modelGradedChartPullbackZero W x) ⊆ K ∧
      ∃ G : ℕ → ComplexVector n → modelGradedFiber n,
        (∀ j, ContDiff ℝ ∞ (G j)) ∧ (∀ j, tsupport (G j) ⊆ K) ∧
        Tendsto (fun j => ∫ z, ‖G j z - modelGradedChartPullbackZero A x z‖ ^ 2 ∂lebesgueC n)
          atTop (𝓝 0) ∧
        Tendsto (fun j => ∫ z,
          ‖modelDiracJetCLM g.form x z (G j z, fderiv ℝ (G j) z) -
            modelGradedChartPullbackZero W x z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  letI : (lebesgueC n).IsNegInvariant := by rw [lebesgueC_eq_volume]; infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  letI : SigmaFinite (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  let U := modelGradedChartPullbackZero A x
  let V := modelGradedChartPullbackZero W x
  let u := fun z c => b.repr (U z) c
  let w := fun z r => b.repr (V z) r
  let a := diracScalarDerivativeCoefficient g.form x b
  let q := diracScalarValueCoefficient g.form x b
  have hU := modelGradedChartPullbackZero_properties g μ hμ A hA hcA x hAx b
  have hV := modelGradedChartPullbackZero_properties g μ hμ W hW hcW x hWx b
  choose Ac Kc hAc hKc using fun r c i => compact_contDiff_coefficient_bounds
    (fun z => χ z * a r c i z) (hAe r c i) hcχ.mul_right
  choose Bc Kb hBc hKb using fun r c => compact_contDiff_coefficient_bounds
    (fun z => χ z * q r c z) (hBe r c) hcχ.mul_right
  have hR (r c : α) (i : RIdx n) :=
    diracScalar_cutoff_derivative_properties g x b χ hχ hcχ hχO r c i
  choose Rc Kr hRc hKr using fun r c i => compact_contDiff_coefficient_bounds
    (fun z => a r c i z * fderiv ℝ χ z (realModelBasis n i)) (hR r c i).1 (hR r c i).2.1
  have hRc0 (r c : α) (i : RIdx n) : 0 ≤ Rc r c i :=
    (norm_nonneg _).trans (hRc r c i 0)
  obtain ⟨ρ, hρ, hcρ, hρ0, hρ1⟩ := exists_model_friedrichs_mollifier n
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j ≤ 1 := by
    dsimp [ε]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcu (c : α) : HasCompactSupport (fun z => u z c) :=
    hU.1.comp_left (g := fun P : modelGradedFiber n => b.repr P c) (by simp)
  have hcw (r : α) : HasCompactSupport (fun z => w z r) :=
    hV.1.comp_left (g := fun P : modelGradedFiber n => b.repr P r) (by simp)
  let Us : ℕ → ComplexVector n → α → ℝ := fun j z c =>
    (MeasureTheory.convolution (rescaledFriedrichsMollifier ρ (ε j)) (fun y => u y c)
      (ContinuousLinearMap.lsmul ℝ ℝ) (lebesgueC n)) z
  have hmol := firstOrderSystemWeakEquation_mollifier_graph_tendsto
    (lebesgueC n) (realModelBasis n) (fun r c i z => χ z * a r c i z)
    (fun r c z => χ z * q r c z)
    (fun r c i => (hAe r c i).of_le (by simp)) Kc hKc Ac hAc
    (fun r c => (hBe r c).continuous) Bc hBc u w hU.2.2.2 hcu hV.2.2.2 hcw hweak
    ρ hρ hcρ hρ0 hρ1 ε hε hε1 htε
  change (∀ j c, ContDiff ℝ ∞ (fun z => Us j z c) ∧ HasCompactSupport (fun z => Us j z c)) ∧
    (∀ c, Tendsto (fun j => ∫ z, ‖Us j z c - u z c‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0)) ∧
    ∀ r, (∀ j, MemLp (fun z => firstOrderSystemApply (realModelBasis n)
      (fun r c i z => χ z * a r c i z) (fun r c z => χ z * q r c z) (Us j) z r) 2 (lebesgueC n)) ∧
      Tendsto (fun j => ∫ z, ‖firstOrderSystemApply (realModelBasis n)
        (fun r c i z => χ z * a r c i z) (fun r c z => χ z * q r c z) (Us j) z r - w z r‖ ^ 2
          ∂lebesgueC n) atTop (𝓝 0) at hmol
  have hχu (z : ComplexVector n) (c : α) : χ z * u z c = u z c := by
    by_cases hz : U z = 0
    · simp [u, hz]
    · rw [(hχK z (Or.inl (subset_tsupport U hz))).1, one_mul]
  have hχdu (z : ComplexVector n) (c : α) (i : RIdx n) :
      fderiv ℝ χ z (realModelBasis n i) * u z c = 0 := by
    by_cases hz : U z = 0
    · simp [u, hz]
    · rw [(hχK z (Or.inl (subset_tsupport U hz))).2, ContinuousLinearMap.zero_apply, zero_mul]
  have hχC (z : ComplexVector n) : ‖χ z‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hχrange z).1]
    exact (hχrange z).2
  have hcut := firstOrderSystemApply_cutoff_graph_tendsto (lebesgueC n) (realModelBasis n) a q
    χ (hχ.differentiable (by simp)) hχ.continuous.aestronglyMeasurable 1 zero_le_one hχC u w Us
    (fun j c => (hmol.1 j c).1.differentiable (by simp)) hU.2.2.2
    (fun j c => (hmol.1 j c).1.continuous.memLp_of_hasCompactSupport (hmol.1 j c).2)
    hV.2.2.2 hmol.2.1 (fun j r => (hmol.2.2 r).1 j) (fun r => (hmol.2.2 r).2)
    hχu hχdu (fun r c i => (hR r c i).1.continuous.aestronglyMeasurable) Rc hRc0 hRc
  let G : ℕ → ComplexVector n → modelGradedFiber n := fun j z => ∑ c, (χ z * Us j z c) • b c
  have hG (j : ℕ) : ContDiff ℝ ∞ (G j) := by
    apply ContDiff.sum
    intro c _
    exact (hχ.mul (hmol.1 j c).1).smul contDiff_const
  have hGK (j : ℕ) : tsupport (G j) ⊆ tsupport χ := by
    apply closure_mono
    intro z hz hzero
    exact hz (by simp [G, hzero])
  have hcG (j : ℕ) : HasCompactSupport (G j) :=
    hcχ.of_isClosed_subset (isClosed_tsupport _) (hGK j)
  have hGO (j : ℕ) : tsupport (G j) ⊆ chartTarget x := (hGK j).trans hχO
  have hcoord (j : ℕ) (z : ComplexVector n) (c : α) : b.repr (G j z) c = χ z * Us j z c := by
    exact congrFun (b.repr_sum_self (fun c => χ z * Us j z c)) c
  have hcoords (j : ℕ) : (fun z c => b.repr (G j z) c) = (fun z c => χ z * Us j z c) := by
    funext z c
    exact hcoord j z c
  have hlimA : Tendsto (fun j => ∫ z, ‖G j z - U z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
    apply (integral_sq_tendsto_zero_of_basis_coordinates (lebesgueC n) b
      (fun j z => G j z - U z) ?_ ?_).2
    · intro j c
      exact (b.coord c).toContinuousLinearMap.comp_memLp'
        (((hG j).continuous.memLp_of_hasCompactSupport (hcG j)).sub hU.2.2.1)
    · intro c
      simpa only [map_sub, Finsupp.sub_apply, hcoord] using hcut.1 c
  let H := fun j z => modelDiracJetCLM g.form x z (G j z, fderiv ℝ (G j) z)
  have hH (j : ℕ) := modelDiracJetCLM_compact_apply_properties g x (G j) (hG j) (hcG j) (hGO j)
  have houtput (j : ℕ) (z : ComplexVector n) (r : α) : b.repr (H j z) r =
      firstOrderSystemApply (realModelBasis n) a q (fun z c => χ z * Us j z c) z r := by
    have hh := (modelDiracJetCLM_scalar_apply g.form x b (G j) z
      ((hG j).differentiable (by simp) z) r).symm
    rw [hcoords j] at hh
    exact hh
  have hlimW : Tendsto (fun j => ∫ z, ‖H j z - V z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
    apply (integral_sq_tendsto_zero_of_basis_coordinates (lebesgueC n) b
      (fun j z => H j z - V z) ?_ ?_).2
    · intro j r
      exact (b.coord r).toContinuousLinearMap.comp_memLp'
        (((hH j).1.continuous.memLp_of_hasCompactSupport (hH j).2.1).sub hV.2.2.1)
    · intro r
      simpa only [map_sub, Finsupp.sub_apply, houtput] using (hcut.2 r).2
  have hUK : tsupport U ⊆ tsupport χ := fun z hz =>
    subset_tsupport χ (by change χ z ≠ 0; rw [(hχK z (Or.inl hz)).1]; exact one_ne_zero)
  have hVK : tsupport V ⊆ tsupport χ := fun z hz =>
    subset_tsupport χ (by change χ z ≠ 0; rw [(hχK z (Or.inr hz)).1]; exact one_ne_zero)
  exact ⟨tsupport χ, hcχ, hχO, hUK, hVK, G, hG, hGK, hlimA, hlimW⟩

/-- A genuine extended Euclidean weak system for compact raw chart fields
produces their exact original minimal Dirac graph. -/
theorem diracMinimalGraph_of_compact_chart_extended_weak_system {α : Type*}
    [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A)
    (hW : OperatorCandidates.GradedL2 g.form μ W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j))
    (hcW : ∀ j, CompactlySupportedRealForm (W j)) (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (hWx : ∀ j, closure {y | W j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (b : Basis α ℝ (modelGradedFiber n))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (hχrange : ∀ z, χ z ∈ Set.Icc (0 : ℝ) 1)
    (hχK : ∀ z ∈ tsupport (modelGradedChartPullbackZero A x) ∪
        tsupport (modelGradedChartPullbackZero W x), χ z = 1 ∧ fderiv ℝ χ z = 0)
    (hAe : ∀ r c i, ContDiff ℝ ∞
      (fun z => χ z * diracScalarDerivativeCoefficient g.form x b r c i z))
    (hBe : ∀ r c, ContDiff ℝ ∞
      (fun z => χ z * diracScalarValueCoefficient g.form x b r c z))
    (hweak : firstOrderSystemWeakEquation (lebesgueC n) (realModelBasis n)
      (fun r c i z => χ z * diracScalarDerivativeCoefficient g.form x b r c i z)
      (fun r c z => χ z * diracScalarValueCoefficient g.form x b r c z)
      (fun z c => b.repr (modelGradedChartPullbackZero A x z) c)
      (fun z r => b.repr (modelGradedChartPullbackZero W x z) r)) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  obtain ⟨K, hcK, hKO, hAK, hWK, G, hG, hGK, htA, htW⟩ :=
    dirac_exists_compact_chart_model_approximants_of_extended_weak_system g μ hμ A W hA hW hcA hcW x hAx hWx b χ hχ hcχ hχO hχrange hχK hAe hBe hweak
  exact diracMinimalGraph_of_compact_chart_approximants g μ hμ A W hA hW
    hcA hcW x hAx hWx hcK hKO hAK hWK G hG hGK htA htW

/-- The actual maximal Dirac equation supplies the exact extended weak
system used by the internal compact model graph approximation theorem. -/
theorem diracMaximalGraph_exists_compact_chart_model_approximants {α : Type*}
    [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j))
    (hcW : ∀ j, CompactlySupportedRealForm (W j)) (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (hWx : ∀ j, closure {y | W j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (b : Basis α ℝ (modelGradedFiber n)) :
    ∃ K : Set (ComplexVector n), IsCompact K ∧ K ⊆ chartTarget x ∧
      tsupport (modelGradedChartPullbackZero A x) ⊆ K ∧
      tsupport (modelGradedChartPullbackZero W x) ⊆ K ∧
      ∃ G : ℕ → ComplexVector n → modelGradedFiber n,
        (∀ j, ContDiff ℝ ∞ (G j)) ∧ (∀ j, tsupport (G j) ⊆ K) ∧
        Tendsto (fun j => ∫ z, ‖G j z - modelGradedChartPullbackZero A x z‖ ^ 2 ∂lebesgueC n)
          atTop (𝓝 0) ∧
        Tendsto (fun j => ∫ z,
          ‖modelDiracJetCLM g.form x z (G j z, fderiv ℝ (G j) z) -
            modelGradedChartPullbackZero W x z‖ ^ 2 ∂lebesgueC n) atTop (𝓝 0) := by
  obtain ⟨χ, hχ, hcχ, hχO, hχrange, hχK, hAe, hBe, hweak⟩ :=
    diracMaximalGraph_exists_chart_weak_system g μ hμ A W hmax hcA hcW x hAx hWx b
  exact dirac_exists_compact_chart_model_approximants_of_extended_weak_system g μ hμ A W hmax.1 hmax.2.1
    hcA hcW x hAx hWx b χ hχ hcχ hχO hχrange hχK hAe hBe hweak

/-- The exact original maximal Dirac graph is minimal for every rough pair
compactly supported in a single genuine chart. -/
theorem diracMaximalGraph_to_minimal_of_compact_chart
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j))
    (hcW : ∀ j, CompactlySupportedRealForm (W j)) (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (hWx : ∀ j, closure {y | W j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    OperatorCandidates.DiracMinimalGraph g.form μ A W := by
  classical
  obtain ⟨K, hcK, hKO, hAK, hWK, G, hG, hGK, htA, htW⟩ :=
    diracMaximalGraph_exists_compact_chart_model_approximants g μ hμ A W hmax hcA hcW x hAx hWx
      (Module.finBasis ℝ (modelGradedFiber n))
  exact diracMinimalGraph_of_compact_chart_approximants g μ hμ A W hmax.1 hmax.2.1
    hcA hcW x hAx hWx hcK hKO hAK hWK G hG hGK htA htW

end Yau.LeafProofs.L03
