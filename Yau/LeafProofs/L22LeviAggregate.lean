import Yau.LeafProofs.L22LeviCalculus
import Yau.LeafProofs.L22Second
import Yau.LeafProofs.L22RegularizedMax

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Filter Set

namespace Yau.LeafProofs.L22Aux

theorem continuousLinearMap_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (y : ι → ℝ) :
    L y = ∑ i, L (Pi.single i 1) * y i := by
  have heq : y = ∑ i, y i • Pi.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [heq]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  simp only [smul_eq_mul]
  ring

theorem secondFDeriv_pi_apply {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] {F : E → ι → ℝ} {z : E} (hF : ContDiffAt ℝ 2 F z)
    (i : ι) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun x => F x i)) z v w =
      fderiv ℝ (fderiv ℝ F) z v w i := by
  have hh := L18Aux.secondFDeriv_comp hF
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt v w
  have heq : fderiv ℝ (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) =
      (fun _ => (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
    funext x
    exact ContinuousLinearMap.fderiv _
  rw [heq] at hh
  simpa [Function.comp_def] using hh

/-- The actual complex-line Hessian chain rule for finite smooth branch families. -/
theorem complexLeviQuadratic_aggregate {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ι → ComplexVector n → ℝ} {Φ : (ι → ℝ) → ℝ} {z : ComplexVector n}
    (hg : ∀ i, ContDiffAt ℝ 2 (g i) z)
    (hΦ : ContDiffAt ℝ 2 Φ (fun i => g i z)) (v : ComplexVector n) :
    complexLeviQuadratic (fun x => Φ (fun i => g i x)) z v =
      (∑ i, fderiv ℝ Φ (fun i => g i z) (Pi.single i 1) * complexLeviQuadratic (g i) z v) +
      (fderiv ℝ (fderiv ℝ Φ) (fun i => g i z)
          (fderiv ℝ (fun x i => g i x) z v) (fderiv ℝ (fun x i => g i x) z v) +
        fderiv ℝ (fderiv ℝ Φ) (fun i => g i z)
          (fderiv ℝ (fun x i => g i x) z (Complex.I • v))
          (fderiv ℝ (fun x i => g i x) z (Complex.I • v))) / 4 := by
  have hG : ContDiffAt ℝ 2 (fun x i => g i x) z := contDiffAt_pi.2 hg
  have hchain (w : ComplexVector n) := L18Aux.secondFDeriv_comp hG hΦ w w
  have hcoord (w : ComplexVector n) (i : ι) :
      fderiv ℝ (fderiv ℝ (fun x i => g i x)) z w w i =
        fderiv ℝ (fderiv ℝ (g i)) z w w :=
    (secondFDeriv_pi_apply hG i w w).symm
  have hlin (w : ComplexVector n) :
      fderiv ℝ Φ (fun i => g i z) (fderiv ℝ (fderiv ℝ (fun x i => g i x)) z w w) =
        ∑ i, fderiv ℝ Φ (fun i => g i z) (Pi.single i 1) *
          fderiv ℝ (fderiv ℝ (g i)) z w w := by
    rw [continuousLinearMap_pi_sum]
    simp only [hcoord]
  unfold complexLeviQuadratic
  change (fderiv ℝ (fderiv ℝ (Φ ∘ fun x i => g i x)) z v v +
    fderiv ℝ (fderiv ℝ (Φ ∘ fun x i => g i x)) z (Complex.I • v) (Complex.I • v)) / 4 = _
  rw [hchain, hchain, hlin, hlin]
  simp only [← mul_div_assoc, mul_add, Finset.sum_add_distrib, ← Finset.sum_div]
  ring

/-- Convex, monotone, translation-equivariant smooth aggregation preserves strict Levi positivity. -/
theorem complexLeviQuadratic_aggregate_pos {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ι → ComplexVector n → ℝ} {Φ : (ι → ℝ) → ℝ} {z : ComplexVector n}
    (hg : ∀ i, ContDiffAt ℝ 2 (g i) z) (hΦ : ContDiff ℝ 2 Φ)
    (hconv : ConvexOn ℝ univ Φ) (hmono : Monotone Φ)
    (htrans : ∀ (y : ι → ℝ) (c : ℝ), Φ (fun i => y i + c) = Φ y + c)
    (hpos : ∀ i v, v ≠ 0 → 0 < complexLeviQuadratic (g i) z v)
    {v : ComplexVector n} (hv : v ≠ 0) :
    0 < complexLeviQuadratic (fun x => Φ (fun i => g i x)) z v := by
  let y : ι → ℝ := fun i => g i z
  let a : ι → ℝ := fun i => fderiv ℝ Φ y (Pi.single i 1)
  have ha (i : ι) : 0 ≤ a i :=
    fderiv_coordinate_nonneg (hΦ.differentiable (by norm_num) y) hmono i
  have hsum : ∑ i, a i = 1 :=
    sum_fderiv_coordinate_eq_one (hΦ.differentiable (by norm_num) y) (htrans y)
  have hex : ∃ i, 0 < a i := by
    by_contra hn
    push Not at hn
    have hz : ∑ i, a i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hn i) (ha i))
    linarith
  obtain ⟨i, hi⟩ := hex
  have hspos : 0 < ∑ j, a j * complexLeviQuadratic (g j) z v := by
    apply Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (le_of_lt (hpos j v hv)))
    exact ⟨i, Finset.mem_univ _, mul_pos hi (hpos i v hv)⟩
  rw [complexLeviQuadratic_aggregate hg hΦ.contDiffAt]
  apply add_pos_of_pos_of_nonneg hspos
  apply div_nonneg _ (by norm_num)
  exact add_nonneg (hessian_nonneg_of_convex hΦ hconv _ _)
    (hessian_nonneg_of_convex hΦ hconv _ _)

/-- The aggregate positivity theorem in the frozen Levi matrix API. -/
theorem leviC_posDef_aggregate {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : ι → ComplexVector n → ℝ} {Φ : (ι → ℝ) → ℝ} {z : ComplexVector n}
    (hg : ∀ i, ContDiffAt ℝ 2 (g i) z) (hΦ : ContDiff ℝ 2 Φ)
    (hconv : ConvexOn ℝ univ Φ) (hmono : Monotone Φ)
    (htrans : ∀ (y : ι → ℝ) (c : ℝ), Φ (fun i => y i + c) = Φ y + c)
    (hpos : ∀ i, (leviC (g i) z).PosDef) :
    (leviC (fun x => Φ (fun i => g i x)) z).PosDef := by
  apply (leviC_posDef_iff (hΦ.contDiffAt.comp z (contDiffAt_pi.2 hg))).2
  intro v hv
  exact complexLeviQuadratic_aggregate_pos hg hΦ hconv hmono htrans
    (fun i => (leviC_posDef_iff (hg i)).1 (hpos i)) hv

/-- Finite regularized maxima of genuinely C² strict branches have positive Levi matrix. -/
theorem leviC_posDef_regularizedMaxCoords {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (δ : ι → ℝ) {g : ι → ComplexVector n → ℝ} {z : ComplexVector n}
    (hg : ∀ i, ContDiffAt ℝ 2 (g i) z) (hpos : ∀ i, (leviC (g i) z).PosDef) :
    (leviC (fun x => regularizedMaxCoords δ (fun i => g i x)) z).PosDef := by
  apply leviC_posDef_aggregate hg ((regularizedMaxCoords_smooth δ).of_le (by simp))
    (regularizedMaxCoords_convex δ) (regularizedMaxCoords_monotone δ)
    (regularizedMaxCoords_add_const δ) hpos

end Yau.LeafProofs.L22Aux
