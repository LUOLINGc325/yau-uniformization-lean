import Yau.Proofs.C04BoundedGeometryChartsActualMetric

/-! The actual complex coefficients are fixed linear functionals of the same Gram model. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff InnerProductSpace
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

abbrev RealGramSpace (n : ℕ) := ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ

def realGramComplexEntry (a b : Fin n) : RealGramSpace n →L[ℝ] ℂ :=
  let ev (u v : ComplexVector n) : RealGramSpace n →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp
      (ContinuousLinearMap.apply ℝ (ComplexVector n →L[ℝ] ℝ) u)
  (1 / 2 : ℝ) • (Complex.ofRealCLM.comp (ev (stdVec a) (stdVec b))) -
    Complex.I • ((1 / 2 : ℝ) • (Complex.ofRealCLM.comp (ev (stdVec a) (Complex.I • stdVec b))))

theorem realGramComplexEntry_apply (a b : Fin n) (H : RealGramSpace n) :
    realGramComplexEntry a b H = (H (stdVec a) (stdVec b) / 2 : ℝ) -
      Complex.I * (H (stdVec a) (Complex.I • stdVec b) / 2 : ℝ) := by
  simp [realGramComplexEntry, Complex.real_smul, smul_eq_mul, div_eq_mul_inv] <;> ring

def normalChartGram (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z : ComplexVector n) : RealGramSpace n :=
  C04Aux.normalModelMetric ((radialCoframe g p U (normalizedInverseParameter e L d z)).comp
    (fderiv ℝ (normalizedInverseParameter e L d) z))

theorem normalChartMap_pullback_eq_gram_entry (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (e : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (L : ComplexVector n →L[ℝ] ComplexVector n) (d : ℝ) (z : ComplexVector n) (a b : Fin n)
    (hparam : DifferentiableAt ℝ (normalizedInverseParameter e L d) z)
    (hf : MDifferentiableAt (ComplexModel n) (ComplexModel n) (normalChartMap g p U e L d) z) :
    pullbackMat g.form (normalChartMap g p U e L d) z a b =
      realGramComplexEntry a b (normalChartGram g p U e L d z) := by
  rw [realGramComplexEntry_apply]
  exact normalChartMap_pullback_entry g p U hU e L d z a b hparam hf

theorem gram_entry_iteratedFDeriv_le (O : Set (ComplexVector n)) (hO : IsOpen O)
    (H : ComplexVector n → RealGramSpace n) (hH : ContDiffOn ℝ ∞ H O)
    (f : ComplexVector n → ℂ) (a b : Fin n)
    (heq : Set.EqOn f (fun x => realGramComplexEntry a b (H x)) O)
    (m : ℕ) (z : ComplexVector n) (hz : z ∈ O) :
    ‖iteratedFDeriv ℝ m f z‖ ≤ ‖realGramComplexEntry a b‖ * ‖iteratedFDeriv ℝ m H z‖ := by
  have he : f =ᶠ[𝓝 z] (fun x => realGramComplexEntry a b (H x)) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨O, hO.mem_nhds hz, heq⟩
  rw [(he.iteratedFDeriv ℝ m).self_of_nhds]
  exact (realGramComplexEntry a b).norm_iteratedFDeriv_comp_left
    (hH.contDiffAt (hO.mem_nhds hz)) (by simp)

def gramEntryBudget (n : ℕ) : ℝ := 1 + ∑ a : Fin n, ∑ b : Fin n, ‖realGramComplexEntry a b‖

theorem gramEntryBudget_one_le (n : ℕ) : 1 ≤ gramEntryBudget n := by
  unfold gramEntryBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem realGramComplexEntry_norm_le (a b : Fin n) :
    ‖realGramComplexEntry a b‖ ≤ gramEntryBudget n := by
  have h₁ := Finset.single_le_sum (f := fun b : Fin n => ‖realGramComplexEntry a b‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
  have h₂ := Finset.single_le_sum (f := fun a : Fin n => ∑ b : Fin n, ‖realGramComplexEntry a b‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  exact (h₁.trans h₂).trans (le_add_of_nonneg_left (by norm_num))

def gramDerivativeBudget (n : ℕ) (B : ℕ → ℝ) (m : ℕ) : ℝ :=
  gramEntryBudget n * (1 + ∑ j ∈ Finset.range (m + 1), B j)

theorem gramDerivativeBudget_pos (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) (m : ℕ) :
    0 < gramDerivativeBudget n B m := by
  have hE : 0 < gramEntryBudget n := lt_of_lt_of_le zero_lt_one (gramEntryBudget_one_le n)
  have hsum : 0 ≤ ∑ j ∈ Finset.range (m + 1), B j :=
    Finset.sum_nonneg fun j _ => (hB j).le
  unfold gramDerivativeBudget
  exact mul_pos hE (by positivity)

theorem pullbackDerivBound_of_gram_model (k : HermitianField M)
    (Phi : ComplexVector n → M.Carrier) (rc : ℝ) (hrc : 0 < rc)
    (H : ComplexVector n → RealGramSpace n)
    (hH : ContDiffOn ℝ ∞ H (Metric.ball (0 : ComplexVector n) rc))
    (heq : ∀ z ∈ Metric.ball (0 : ComplexVector n) rc, ∀ a b : Fin n,
      pullbackMat k Phi z a b = realGramComplexEntry a b (H z))
    (B : ℕ → ℝ) (hB : ∀ m, 0 < B m)
    (hjet : ∀ m z, z ∈ Metric.ball (0 : ComplexVector n) (rc / 2) →
      ‖iteratedFDeriv ℝ m H z‖ ≤ B m) (m : ℕ) :
    PullbackDerivBound k Phi (rc / 2) m (gramDerivativeBudget n B m) := by
  intro j hj z hz a b
  have hzo : z ∈ Metric.ball (0 : ComplexVector n) rc :=
    Metric.ball_subset_ball (by linarith) hz
  have hh := gram_entry_iteratedFDeriv_le (Metric.ball (0 : ComplexVector n) rc)
    Metric.isOpen_ball H hH (fun x => pullbackMat k Phi x a b) a b
    (fun x hx => heq x hx a b) j z hzo
  have hsum : B j ≤ 1 + ∑ k ∈ Finset.range (m + 1), B k :=
    (Finset.single_le_sum (f := B) (fun k _ => (hB k).le)
      (Finset.mem_range.mpr (by omega : j < m + 1))).trans
      (le_add_of_nonneg_left (by norm_num))
  exact hh.trans ((mul_le_mul (realGramComplexEntry_norm_le a b) (hjet j z hz)
    (norm_nonneg _) (le_trans zero_le_one (gramEntryBudget_one_le n))).trans
      (mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one (gramEntryBudget_one_le n))))

end Yau.Proofs.C04ChartsAux
