import Yau.LeafProofs.L14TwoChartGeometry
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
section TwoPairFrameAlgebra
variable {V W ι : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
  [Fintype ι] [DecidableEq ι]

theorem twoTensorFramePairing_add_left (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B C : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    twoTensorFramePairing hV hW hol anti (A+B) C =
      twoTensorFramePairing hV hW hol anti A C + twoTensorFramePairing hV hW hol anti B C := by
  simp only [twoTensorFramePairing_eq_sum, AlternatingMap.add_apply, hW.map_add_left,
    add_div, mul_add, Finset.sum_add_distrib]

theorem twoTensorFramePairing_add_right (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B C : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    twoTensorFramePairing hV hW hol anti A (B+C) =
      twoTensorFramePairing hV hW hol anti A B + twoTensorFramePairing hV hW hol anti A C := by
  simp only [twoTensorFramePairing_eq_sum, AlternatingMap.add_apply, hW.map_add_right,
    add_div, mul_add, Finset.sum_add_distrib]

theorem twoTensorFramePairing_smul_left (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (c : ℂ) (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    twoTensorFramePairing hV hW hol anti (c • A) B = star c * twoTensorFramePairing hV hW hol anti A B := by
  simp only [twoTensorFramePairing_eq_sum, AlternatingMap.smul_apply, hW.map_smul_left]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem twoTensorFramePairing_smul_right (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (c : ℂ) (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    twoTensorFramePairing hV hW hol anti A (c • B) = c * twoTensorFramePairing hV hW hol anti A B := by
  simp only [twoTensorFramePairing_eq_sum, AlternatingMap.smul_apply, hW.map_smul_right]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem twoTensorFramePairing_conj_symm (hV : Yau.HermitianInnerProduct V) (hW : Yau.HermitianInnerProduct W)
    (hol anti : Basis ι ℂ V) (A B : V [⋀^Fin 2]→ₗ[ℝ] (V [⋀^ι]→ₗ[ℂ] W)) :
    star (twoTensorFramePairing hV hW hol anti B A) = twoTensorFramePairing hV hW hol anti A B := by
  let G := (hermitianGram hV anti)⁻¹
  have hG (i j : ι) : star (G i j) = G j i := (hermitianGram_posDef hV anti).inv.isHermitian.apply j i
  have hWstar (u v : W) : star (hW.toFun v u) = hW.toFun u v := (hW.conjugate_symmetric u v).symm
  have hs : star (∑ i, ∑ k, ∑ j, ∑ l, G i k * G j l *
      hW.toFun (twoTensorHolEvaluation B hol ![anti i,anti j]) (twoTensorHolEvaluation A hol ![anti k,anti l])) =
      ∑ i, ∑ k, ∑ j, ∑ l, G i k * G j l *
        hW.toFun (twoTensorHolEvaluation A hol ![anti i,anti j]) (twoTensorHolEvaluation B hol ![anti k,anti l]) := by
    simp_rw [star_sum, star_mul, hG, hWstar]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hd : star (((hermitianGram hV hol).det.re : ℂ)⁻¹) = ((hermitianGram hV hol).det.re : ℂ)⁻¹ := by simp
  have hh : star (1 / 2 : ℂ) = 1 / 2 := by simp
  change star ((1 / 2 : ℂ) * ((hermitianGram hV hol).det.re : ℂ)⁻¹ * _) =
    (1 / 2 : ℂ) * ((hermitianGram hV hol).det.re : ℂ)⁻¹ * _
  rw [star_mul, star_mul, hs, hd, hh]
  ring

end TwoPairFrameAlgebra

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem twoFormPairing_add_left (g : HermitianField M) (h : Metric E)
    (u v w : NQForm E 2) (x : M.Carrier) :
    twoFormPairing E g h (u+v) w x = twoFormPairing E g h u w x + twoFormPairing E g h v w x :=
  twoTensorFramePairing_add_left (g x) (h x) _ _ (u x).1 (v x).1 (w x).1

theorem twoFormPairing_add_right (g : HermitianField M) (h : Metric E)
    (u v w : NQForm E 2) (x : M.Carrier) :
    twoFormPairing E g h u (v+w) x = twoFormPairing E g h u v x + twoFormPairing E g h u w x :=
  twoTensorFramePairing_add_right (g x) (h x) _ _ (u x).1 (v x).1 (w x).1

theorem twoFormPairing_smul_left (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u v : NQForm E 2) (x : M.Carrier) :
    twoFormPairing E g h (c • u) v x = star c * twoFormPairing E g h u v x :=
  twoTensorFramePairing_smul_left (g x) (h x) _ _ c (u x).1 (v x).1

theorem twoFormPairing_smul_right (g : HermitianField M) (h : Metric E)
    (c : ℂ) (u v : NQForm E 2) (x : M.Carrier) :
    twoFormPairing E g h u (c • v) x = c * twoFormPairing E g h u v x :=
  twoTensorFramePairing_smul_right (g x) (h x) _ _ c (u x).1 (v x).1

theorem twoFormPairing_conj_symm (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 2) (x : M.Carrier) :
    star (twoFormPairing E g h v u x) = twoFormPairing E g h u v x :=
  twoTensorFramePairing_conj_symm (g x) (h x) _ _ (u x).1 (v x).1

def twoFormPointPreInner (g : HermitianField M) (h : Metric E) (x : M.Carrier) :
    PreInnerProductSpace.Core ℂ (NQForm E 2) where
  inner u v := twoFormPairing E g h u v x
  conj_inner_symm u v := twoFormPairing_conj_symm E g h u v x
  re_inner_nonneg u := by
    change 0 ≤ (twoFormPairing E g h u u x).re
    rw [twoFormPairing_self_re (r := r) E g h u x]
    exact formNormSq_two_nonneg E g h u x
  add_left u v w := twoFormPairing_add_left E g h u v w x
  smul_left u v c := twoFormPairing_smul_left E g h c u v x

theorem twoFormPairing_cauchySchwarz (g : HermitianField M) (h : Metric E)
    (u v : NQForm E 2) (x : M.Carrier) :
    Complex.normSq (twoFormPairing E g h u v x) ≤
      BundleDbar.formNormSq (r := r) E g h u x * BundleDbar.formNormSq (r := r) E g h v x := by
  letI : PreInnerProductSpace.Core ℂ (NQForm E 2) := twoFormPointPreInner (r := r) E g h x
  have ht := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) u v
  change ‖twoFormPairing E g h u v x‖ * ‖twoFormPairing E g h v u x‖ ≤
    (twoFormPairing E g h u u x).re * (twoFormPairing E g h v v x).re at ht
  rw [twoFormPairing_self_re (r := r) E g h u x, twoFormPairing_self_re (r := r) E g h v x] at ht
  have hn : ‖twoFormPairing E g h v u x‖ = ‖twoFormPairing E g h u v x‖ := by
    simpa only [norm_star] using congrArg norm (twoFormPairing_conj_symm E g h u v x)
  rw [hn] at ht
  simpa only [Complex.normSq_eq_norm_sq, pow_two] using ht

end Yau.LeafProofs.L14Aux

namespace Yau.LeafProofs.L14Aux

open BundleDbar Filter

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

end Yau.LeafProofs.L14Aux
