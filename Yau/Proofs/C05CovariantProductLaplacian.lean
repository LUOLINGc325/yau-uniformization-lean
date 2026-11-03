import Yau.Proofs.C05CovariantPairLaplacian
import Yau.LeafProofs.L23TensorProductCalculus

/-! The second covariant product rule for the actual connection, with
both derivative slots retained. -/

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n r s : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem covariantD_twice_concatProduct (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j : RIdx n)
    (v : Fin (r + s) → RIdx n) :
    covariantD k c (covariantD k c (fun w => tensorConcatProduct (A w) (B w))) z
        (Fin.cons i (Fin.cons j v)) =
      tensorConcatProduct
        (fun u => covariantD k c (covariantD k c A) z (Fin.cons i (Fin.cons j u))) (B z) v +
      tensorConcatProduct (fun u => covariantD k c A z (Fin.cons j u))
        (fun u => covariantD k c B z (Fin.cons i u)) v +
      tensorConcatProduct (fun u => covariantD k c A z (Fin.cons i u))
        (fun u => covariantD k c B z (Fin.cons j u)) v +
      tensorConcatProduct (A z)
        (fun u => covariantD k c (covariantD k c B) z (Fin.cons i (Fin.cons j u))) v := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  let Aj := fun w u => covariantD k c A w (Fin.cons j u)
  let Bj := fun w u => covariantD k c B w (Fin.cons j u)
  let P := fun w => tensorConcatProduct (A w) (B w)
  have hAj (u : Fin r → RIdx n) := covariantD_contDiffOn k hk c A hA (Fin.cons j u)
  have hBj (u : Fin s → RIdx n) := covariantD_contDiffOn k hk c B hB (Fin.cons j u)
  have hAd (u : Fin r → RIdx n) := ((hA u).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hBd (u : Fin s → RIdx n) := ((hB u).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hAjd (u : Fin r → RIdx n) := ((hAj u).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hBjd (u : Fin s → RIdx n) := ((hBj u).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have he : (fun w u => covariantD k c P w (Fin.cons j u)) =ᶠ[𝓝 z]
      (fun w => tensorConcatProduct (Aj w) (B w) + tensorConcatProduct (A w) (Bj w)) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    funext u
    exact covariantD_concatProduct_cons k c A B w
      (fun v => ((hA v).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp))
      (fun v => ((hB v).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp)) j u
  have hd := covariantD_eventuallyEq k c _ _ z he
  have hprod₁ (u : Fin (r + s) → RIdx n) : DifferentiableAt ℝ
      (fun w => tensorConcatProduct (Aj w) (B w) u) z :=
    (hAjd _).mul (hBd _)
  have hprod₂ (u : Fin (r + s) → RIdx n) : DifferentiableAt ℝ
      (fun w => tensorConcatProduct (A w) (Bj w) u) z :=
    (hAd _).mul (hBjd _)
  rw [covariantD_add_at k c _ _ z hprod₁ hprod₂] at hd
  have hdi := congrFun hd (Fin.cons i v)
  simp only [Pi.add_apply] at hdi
  rw [covariantD_concatProduct_cons k c Aj B z hAjd hBd i v,
    covariantD_concatProduct_cons k c A Bj z hAd hBjd i v] at hdi
  rw [covariantD_twice_cons_split k c P z i j v, hdi]
  dsimp only [P]
  simp_rw [covariantD_twice_cons_split k c A z i j,
    covariantD_twice_cons_split k c B z i j,
    covariantD_concatProduct_cons k c A B z hAd hBd]
  simp only [tensorConcatProduct, Pi.add_apply, mul_sub, sub_mul, add_mul, mul_add,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
  dsimp only [Aj, Bj]
  ring

theorem roughLap_concatProduct (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r)
    (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (v : Fin (r + s) → RIdx n) :
    roughLap k c (fun w => tensorConcatProduct (A w) (B w)) z v =
      tensorConcatProduct (roughLap k c A z) (B z) v +
      tensorConcatProduct (A z) (roughLap k c B z) v +
      2 * ∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j * tensorConcatProduct
        (fun u => covariantD k c A z (Fin.cons i u))
        (fun u => covariantD k c B z (Fin.cons j u)) v := by
  have hcross : (∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j * tensorConcatProduct
      (fun u => covariantD k c A z (Fin.cons j u))
      (fun u => covariantD k c B z (Fin.cons i u)) v) =
      ∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j * tensorConcatProduct
        (fun u => covariantD k c A z (Fin.cons i u))
        (fun u => covariantD k c B z (Fin.cons j u)) v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(Yau.LeafProofs.L18Aux.realMetricFn_isSymm k c z).inv.apply i j]
  have hleft : (∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j * tensorConcatProduct
      (fun u => covariantD k c (covariantD k c A) z (Fin.cons i (Fin.cons j u))) (B z) v) =
      tensorConcatProduct (roughLap k c A z) (B z) v := by
    simp only [tensorConcatProduct, roughLap, Finset.sum_mul, mul_assoc]
  have hright : (∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j * tensorConcatProduct (A z)
      (fun u => covariantD k c (covariantD k c B) z (Fin.cons i (Fin.cons j u))) v) =
      tensorConcatProduct (A z) (roughLap k c B z) v := by
    simp only [tensorConcatProduct, roughLap, Finset.mul_sum, mul_left_comm]
  change (∑ i, ∑ j, (realMetricFn k c z)⁻¹ i j *
    covariantD k c (covariantD k c (fun w => tensorConcatProduct (A w) (B w))) z
      (Fin.cons i (Fin.cons j v))) = _
  simp_rw [covariantD_twice_concatProduct k hk c A B hA hB hz]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hcross, hleft, hright]
  ring

end Yau.Proofs.C05Aux
