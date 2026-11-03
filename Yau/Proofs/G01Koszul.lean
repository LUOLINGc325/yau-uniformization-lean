import Yau.Proofs.G01ConnectionJ

noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
open Yau Yau.LeafProofs

/-- Finite Koszul uniqueness uses explicit symmetry and the actual metric derivative. -/
theorem koszul_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (D C : ι → Matrix ι ι ℝ)
    (hG : G.IsSymm) (hC : ∀ a b d, C a d b = C b d a)
    (hD : ∀ a, D a = (C a)ᵀ * G + G * C a) (a b c : ι) :
    (∑ d, C a d b * G d c) = (D a b c + D b a c - D c a b) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  rw [hD a, hD b, hD c]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [hC b a d, hC c a d, hC c b d,
    show G b d = G d b from (hG.apply b d).symm]
  ring

variable {n : ℕ} {M : ComplexManifold n}

/-- A symmetric, metric-compatible coefficient family is the computed Levi-Civita family. -/
theorem connectionMatrix_eq_of_compatible (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (C : RIdx n → Matrix (RIdx n) (RIdx n) ℝ)
    (hC : ∀ a b d, C a d b = C b d a)
    (hD : ∀ a, L12Aux.matrixDirectionalDerivative (fun w => realMetricFn h x w) z
      (realVec a) = (C a)ᵀ * realMetricFn h x z + realMetricFn h x z * C a)
    (a : RIdx n) : L12Aux.connectionMatrix h x z a = C a := by
  let G := realMetricFn h x z
  ext c b
  let W : RIdx n → ℝ := fun d => christoffel h x z d a b - C a d b
  have hvec : G *ᵥ W = 0 := by
    funext k
    have hl := L23Aux.christoffel_metric_contraction h hs x z hz a b k
    have hc := koszul_contraction G
      (fun a => L12Aux.matrixDirectionalDerivative (fun w => realMetricFn h x w) z (realVec a))
      C (L12Aux.realMetricFn_isSymm h x z) hC hD a b k
    have he : (∑ d, christoffel h x z d a b * G d k) = ∑ d, C a d b * G d k :=
      hl.trans hc.symm
    change (∑ d, G k d * W d) = 0
    calc
      _ = (∑ d, christoffel h x z d a b * G d k) - ∑ d, C a d b * G d k := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro d _
        rw [show G k d = G d k from (L12Aux.realMetricFn_isSymm h x z).apply d k]
        dsimp [W]
        ring
      _ = 0 := sub_eq_zero.mpr he
  have hinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h x z hz).det_pos.ne')
  have hW : W = 0 := by
    calc
      W = G⁻¹ *ᵥ (G *ᵥ W) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      _ = 0 := by rw [hvec, Matrix.mulVec_zero]
  exact sub_eq_zero.mp (congrFun hW c)

end Yau.NodeProofs.G01Aux
