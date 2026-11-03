import Yau.Proofs.Y05TaylorBounds
import Yau.Proofs.U02AnalyticSeries
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Filter Set
open scoped ContDiff Topology BigOperators

variable {n : ℕ}

theorem canonical_series_of_analyticAt {f : ComplexVector n → ℂ} (hf : AnalyticAt ℂ f 0) :
    HasFPowerSeriesAt f (U02AnalyticAux.complexTaylorSeries f 0) 0 := by
  have hb : ∀ᶠ z in 𝓝 (0 : ComplexVector n), ‖f z‖ < ‖f 0‖ + 1 :=
    hf.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hb)
  have ha : AnalyticOnNhd ℂ f (Metric.ball 0 R) := fun z hz => (hsub hz).1
  exact (U02AnalyticAux.hasFPowerSeriesOnBall_of_complex_contDiffOn_infty hR
    (by positivity : 0 ≤ ‖f 0‖ + 1) ha.contDiffOn_of_completeSpace
    (fun z hz => (hsub hz).2.le)).hasFPowerSeriesAt

def compositionJetConstant (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (d + 1), (Fintype.card (OrderedFinpartition m) : ℝ)

def finiteJetNorm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : ComplexVector n → G) (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (d + 1), ‖iteratedFDeriv ℂ m f 0‖

/-- The vanishing constant term leaves one full factor of the small inner
jet, rather than replacing it by a uniform bound. -/
theorem finiteJetNorm_comp_le
    {F₀ G₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
    [NormedAddCommGroup G₀] [NormedSpace ℂ G₀]
    {f : ComplexVector n → F₀}
    {g : F₀ → G₀} {d : ℕ} {D G δ : ℝ}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hD : 1 ≤ D) (hG : 0 ≤ G)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgb : ∀ m ≤ d, ‖iteratedFDeriv ℂ m g 0‖ ≤ G)
    (hfb : ∀ m, 1 ≤ m → m ≤ d → ‖iteratedFDeriv ℂ m f 0‖ ≤ D * δ) :
    finiteJetNorm (g ∘ f) d ≤ compositionJetConstant d * G * D ^ d * δ := by
  have hDn : 0 ≤ D := le_trans zero_le_one hD
  have hm_bound (m : ℕ) (hm : m ≤ d) :
      ‖iteratedFDeriv ℂ m (g ∘ f) 0‖ ≤
        (Fintype.card (OrderedFinpartition m) : ℝ) * G * D ^ d * δ := by
    by_cases hm0 : m = 0
    · subst m
      simp only [norm_iteratedFDeriv_zero, Function.comp_apply, hf0, hg0, norm_zero]
      positivity
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hgF : ContDiffAt ℂ d g (f 0) := by simpa only [hf0] using hg
    rw [iteratedFDeriv_comp hgF hf (by exact_mod_cast hm), hf0,
      FormalMultilinearSeries.taylorComp]
    apply (norm_sum_le _ _).trans
    have hterm (c : OrderedFinpartition m) :
        ‖FormalMultilinearSeries.compAlongOrderedFinpartition
          (fun j => iteratedFDeriv ℂ j g 0)
          (fun j => iteratedFDeriv ℂ j f 0) c‖ ≤ G * D ^ d * δ := by
      apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
      have hp : (∏ j : Fin c.length, ‖iteratedFDeriv ℂ (c.partSize j) f 0‖) ≤
          D ^ d * δ := by
        calc
          _ ≤ ∏ _j : Fin c.length, D * δ :=
            Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
              (fun j _ => hfb (c.partSize j) (c.partSize_pos j)
                ((c.partSize_le j).trans hm))
          _ = D ^ c.length * δ ^ c.length := by simp only [Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, mul_pow]
          _ ≤ D ^ d * δ := mul_le_mul
            (pow_le_pow_right₀ hD (c.length_le.trans hm))
            (pow_le_of_le_one hδ hδ1 (c.length_pos hmpos).ne')
            (pow_nonneg hδ _) (pow_nonneg hDn _)
      exact (mul_le_mul (hgb c.length (c.length_le.trans hm)) hp
        (Finset.prod_nonneg fun j _ => norm_nonneg _) hG).trans_eq (by ring)
    calc
      _ ≤ ∑ _c : OrderedFinpartition m, G * D ^ d * δ :=
        Finset.sum_le_sum (fun c _ => hterm c)
      _ = _ := by simp; ring
  unfold finiteJetNorm compositionJetConstant
  simp only [Finset.sum_mul]
  exact Finset.sum_le_sum (fun m hm => hm_bound m
    (by have := Finset.mem_range.mp hm; omega))

theorem finiteJetNorm_comp_uniform_le
    {F₀ G₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
    [NormedAddCommGroup G₀] [NormedSpace ℂ G₀]
    {f : ComplexVector n → F₀} {g : F₀ → G₀} {d : ℕ} {D G : ℝ}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0)
    (hf0 : f 0 = 0) (hD : 1 ≤ D) (hG : 0 ≤ G)
    (hgb : ∀ m ≤ d, ‖iteratedFDeriv ℂ m g 0‖ ≤ G)
    (hfb : ∀ m, 1 ≤ m → m ≤ d → ‖iteratedFDeriv ℂ m f 0‖ ≤ D) :
    finiteJetNorm (g ∘ f) d ≤ compositionJetConstant d * G * D ^ d := by
  unfold finiteJetNorm compositionJetConstant
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  have hmd : m ≤ d := by have := Finset.mem_range.mp hm; omega
  have hgF : ContDiffAt ℂ d g (f 0) := by simpa only [hf0] using hg
  rw [iteratedFDeriv_comp hgF hf (by exact_mod_cast hmd), hf0,
    FormalMultilinearSeries.taylorComp]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _c : OrderedFinpartition m, G * D ^ d := by
      apply Finset.sum_le_sum
      intro c hc
      apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
      have hp : (∏ j : Fin c.length, ‖iteratedFDeriv ℂ (c.partSize j) f 0‖) ≤ D ^ d := by
        calc
          _ ≤ ∏ _j : Fin c.length, D :=
            Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
              (fun j _ => hfb (c.partSize j) (c.partSize_pos j)
                ((c.partSize_le j).trans hmd))
          _ = D ^ c.length := by simp
          _ ≤ D ^ d := pow_le_pow_right₀ hD (c.length_le.trans hmd)
      exact mul_le_mul (hgb c.length (c.length_le.trans hmd)) hp
        (Finset.prod_nonneg fun j _ => norm_nonneg _) hG
    _ = _ := by simp; ring

theorem scalarJetNorm_comp_le {f : ComplexVector n → ComplexVector n}
    {g : ComplexVector n → ℂ} {d : ℕ} {D G δ : ℝ}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hD : 1 ≤ D) (hG : 0 ≤ G)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgb : ∀ m ≤ d, ‖iteratedFDeriv ℂ m g 0‖ ≤ G)
    (hfb : ∀ m, 1 ≤ m → m ≤ d → ‖iteratedFDeriv ℂ m f 0‖ ≤ D * δ) :
    scalarJetNorm (g ∘ f) d ≤ compositionJetConstant d * G * D ^ d * δ :=
  finiteJetNorm_comp_le hf hg hf0 hg0 hD hG hδ hδ1 hgb hfb

theorem exists_composed_taylor_bound {f : ComplexVector n → ComplexVector n}
    {g : ComplexVector n → ℂ} {d : ℕ} {D G δ : ℝ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hD : 1 ≤ D) (hG : 0 ≤ G)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgb : ∀ m ≤ d, ‖iteratedFDeriv ℂ m g 0‖ ≤ G)
    (hfb : ∀ m, 1 ≤ m → m ≤ d → ‖iteratedFDeriv ℂ m f 0‖ ≤ D * δ) :
    ∃ B : MvPolynomial (Fin n) ℂ,
      B.totalDegree ≤ d ∧ B.coeff 0 = 0 ∧ ScalarJetEq (scalarEval B) (g ∘ f) d ∧
      Yau.Proofs.Y02Aux.polynomialCoeffNorm B ≤
        scalarTaylorConstant n d * compositionJetConstant d * G * D ^ d * δ := by
  have hgF : AnalyticAt ℂ g (f 0) := by simpa only [hf0] using hg
  have hc := hgF.comp hf
  let B := taylorPolynomial (U02AnalyticAux.complexTaylorSeries (g ∘ f) 0) d
  have hjet : ScalarJetEq (scalarEval B) (g ∘ f) d :=
    scalarJetEq_taylorPolynomial (canonical_series_of_analyticAt hc) d
  refine ⟨B, taylorPolynomial_degree _ _, ?_, hjet, ?_⟩
  · rw [coefficient_zero_of_scalarJetEq hjet, Function.comp_apply, hf0, hg0]
  · exact (coefficientNorm_canonical_taylor (g ∘ f) d).trans
      ((mul_le_mul_of_nonneg_left
        (scalarJetNorm_comp_le hf.contDiffAt hg.contDiffAt hf0 hg0 hD hG hδ hδ1 hgb hfb)
        (Finset.sum_nonneg fun m _ => by positivity)).trans_eq (by
          unfold scalarTaylorConstant
          ring))

end Yau.Proofs.Y05Aux
