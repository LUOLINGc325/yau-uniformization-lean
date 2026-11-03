import Yau.Proofs.C03SourceParallel

/-! Actual source parallel transport supplies both real directions of the
holomorphic variation. Complex parallelism is local along the given path. -/

noncomputable section
open Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem complex_smul_real_decomposition (a : ℂ) (v : ComplexVector n) :
    a • v = a.re • v + a.im • (Complex.I • v) := by
  calc
    a • v = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • v := by rw [Complex.re_add_im]
    _ = a.re • v + a.im • (Complex.I • v) := by
      rw [add_smul, mul_smul]
      rfl

theorem realLinearMap_complex_smul_of_I
    (L : ComplexVector n →L[ℝ] ComplexVector n)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) (a : ℂ) (v : ComplexVector n) :
    L (a • v) = a • L v := by
  rw [complex_smul_real_decomposition a v, map_add, map_smul, map_smul, hI,
    ← complex_smul_real_decomposition a (L v)]

theorem exists_source_parallel_vector (hn : 1 ≤ n)
    (h : HermitianField (ComplexEuclideanManifold n hn)) (hh : MetricSmooth h)
    (γ : ℝ → ComplexVector n) (J : Set ℝ) (hJ : IsOpen J)
    (hγ : ContDiffOn ℝ 3 γ J) (hunit : Icc (0 : ℝ) 1 ⊆ J)
    (hI : ∀ t ∈ J, ∀ v, chartChristoffelBilin h (0 : ComplexVector n)
      (γ t) (deriv γ t) (Complex.I • v) =
      Complex.I • chartChristoffelBilin h (0 : ComplexVector n) (γ t) (deriv γ t) v)
    (V : ComplexVector n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ → ComplexVector n,
      W 0 = V ∧ ContDiffOn ℝ 3 W (Ioo (-δ) (1 + δ)) ∧
      Ioo (-δ) (1 + δ) ⊆ J ∧
      (∀ t ∈ Ioo (-δ) (1 + δ), ∀ a : ℂ,
        HasDerivAt (fun s => a • W s)
          (-chartChristoffelBilin h (0 : ComplexVector n) (γ t) (deriv γ t) (a • W t)) t) ∧
      ∀ t ∈ Ioo (-δ) (1 + δ),
        realMetricInChart h (0 : ComplexVector n) (γ t) (W t) (W t) =
          realMetricInChart h (0 : ComplexVector n) (γ 0) V V := by
  obtain ⟨δ, hδ, P, hP0, hP, hsub, hsol⟩ :=
    exists_source_parallel_matrix hn h hh γ J hJ hγ hunit
  let W : ℝ → ComplexVector n := fun t => P t V
  refine ⟨δ, hδ, W, ?_, hP.clm_apply contDiffOn_const, hsub, ?_, ?_⟩
  · change P 0 V = V
    rw [hP0, ContinuousLinearMap.id_apply]
  · intro t ht a
    have HD : HasDerivAt W
        (-chartChristoffelBilin h (0 : ComplexVector n) (γ t) (deriv γ t) (W t)) t := by
      convert (hsol t ht).1.clm_apply (hasDerivAt_const t V) using 1 <;> simp [W]
    have HA := HD.const_smul a
    have heq := realLinearMap_complex_smul_of_I
      (chartChristoffelBilin h (0 : ComplexVector n) (γ t) (deriv γ t))
      (hI t (hsub ht)) a (W t)
    convert! HA using 1 <;> simp only [smul_neg, heq]
  · intro t ht
    exact (hsol t ht).2 V V

end Yau.Proofs.C03Aux
