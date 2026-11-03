import Yau.LeafProofs.L23ContractionWordTrace
import Yau.LeafProofs.L23TensorTraceCalculus

/-! Covariant Leibniz differentiation of every genuine Word2, including
the inverse metric in both contractions. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux.Word2
set_option backward.isDefEq.respectTransparency false

variable {n r s q : ℕ} {M : ComplexManifold n}

theorem wiredProduct_contDiffOn (w : Word2 r s q) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    (u : Fin (q+4) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => w.wiredProduct (A z) (B z) u) (chartTarget c) := by
  change ContDiffOn ℝ ∞ (fun z =>
    A z (fun j => u (w.inputSlotIndex (Fin.castAdd s j)))*
      B z (fun j => u (w.inputSlotIndex (Fin.natAdd r j)))) (chartTarget c)
  exact (hA _).mul (hB _)

theorem covariantD_wiredProduct_cons (w : Word2 r s q) (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (z : ComplexVector n) (hA : ∀ v, DifferentiableAt ℝ (fun u => A u v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun u => B u v) z) (i : RIdx n) (v : Fin (q+4) → RIdx n) :
    covariantD h c (fun u => w.wiredProduct (A u) (B u)) z (Fin.cons i v)=
      w.wiredProduct (fun u => covariantD h c A z (Fin.cons i u)) (B z) v+
        w.wiredProduct (A z) (fun u => covariantD h c B z (Fin.cons i u)) v := by
  change covariantD h c (fun u v => tensorConcatProduct (A u) (B u) (v ∘ w.inputSlotIndex)) z
    (Fin.cons i v)=_
  rw [covariantD_reindex_cons,covariantD_concatProduct_cons h c A B z hA hB]
  rfl

theorem eval_contDiffOn (w : Word2 r s q) (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c)) (v : Fin q → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => w.eval (realMetricFn h c z)⁻¹ (A z) (B z) v) (chartTarget c) := by
  simp_rw [eval_eq_two_traces]
  exact tensorMetricTrace_contDiffOn h hh c _
    (tensorMetricTrace_contDiffOn h hh c _ (wiredProduct_contDiffOn w c A B hA hB)) v

theorem covariantD_eval (w : Word2 r s q) (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) (v : Fin q → RIdx n) :
    covariantD h c (fun u => w.eval (realMetricFn h c u)⁻¹ (A u) (B u)) z (Fin.cons i v)=
      w.dLeft.eval (realMetricFn h c z)⁻¹ (covariantD h c A z) (B z) (Fin.cons i v)+
        w.dRight.eval (realMetricFn h c z)⁻¹ (A z) (covariantD h c B z) (Fin.cons i v) := by
  have hfield : (fun u => w.eval (realMetricFn h c u)⁻¹ (A u) (B u))=
      (fun u => tensorMetricTrace (realMetricFn h c u)⁻¹
        (tensorMetricTrace (realMetricFn h c u)⁻¹ (w.wiredProduct (A u) (B u)))) := by
    funext u
    exact eval_eq_two_traces w _ _ _
  have hAd (u : Fin r → RIdx n) := ((hA u).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hBd (u : Fin s → RIdx n) := ((hB u).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  rw [hfield,covariantD_twoMetricTraces h hh c _ (wiredProduct_contDiffOn w c A B hA hB) hz i v,
    eval_dLeft,eval_dRight,eval_eq_two_traces,eval_eq_two_traces]
  simp_rw [covariantD_wiredProduct_cons w h c A B z hAd hBd]
  simp only [tensorMetricTrace,mul_add,Finset.sum_add_distrib]

end Yau.LeafProofs.L23Aux.Word2
