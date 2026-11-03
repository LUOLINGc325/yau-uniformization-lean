import Yau.Proofs.C03GlobalGeometry
import Yau.LeafProofs.L23FieldMetricParallelInterval

/-! The global source chart gives genuine parallel matrix fields with the
prescribed initial value along any compact source segment. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem euclidean_chartPt (hn : 1 ≤ n)
    (c z : (ComplexEuclideanManifold n hn).Carrier) : chartPt c z = z := by
  change extChartAt (ComplexModel n) (c : ComplexVector n) z = z
  rw [extChartAt_model_space_eq_id]
  rfl

theorem euclidean_chartSource (hn : 1 ≤ n)
    (c : (ComplexEuclideanManifold n hn).Carrier) :
    (chartAt (ComplexVector n) c).source = univ := by
  change (chartAt (ComplexVector n) (c : ComplexVector n)).source = univ
  rw [chartAt_self_eq]
  rfl

theorem exists_source_parallel_matrix (hn : 1 ≤ n)
    (h : HermitianField (ComplexEuclideanManifold n hn)) (hh : MetricSmooth h)
    (γ : ℝ → ComplexVector n) (J : Set ℝ) (hJ : IsOpen J)
    (hγ : ContDiffOn ℝ 3 γ J) (hunit : Icc (0 : ℝ) 1 ⊆ J) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ → ComplexVector n →L[ℝ] ComplexVector n,
      W 0 = ContinuousLinearMap.id ℝ _ ∧ ContDiffOn ℝ 3 W (Ioo (-δ) (1 + δ)) ∧
      Ioo (-δ) (1 + δ) ⊆ J ∧
      ∀ t ∈ Ioo (-δ) (1 + δ),
        HasDerivAt W ((-chartChristoffelBilin h (0 : ComplexVector n) (γ t) (deriv γ t)).comp (W t)) t ∧
        ∀ v w : ComplexVector n,
          realMetricInChart h (0 : ComplexVector n) (γ t) (W t v) (W t w) =
            realMetricInChart h (0 : ComplexVector n) (γ 0) v w := by
  letI := manifold_realSmooth (ComplexEuclideanManifold n hn)
  have hγM : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J := hγ.contMDiffOn
  have hsrc : MapsTo γ J (chartAt (ComplexVector n)
      (0 : ComplexVector n)).source := by
    rw [euclidean_chartSource hn]
    exact mapsTo_univ _ _
  obtain ⟨δ, hδ, W, hW0, hW, hsol⟩ := exists_chart_parallel_matrix_interval h hh γ (0 : ComplexVector n)
    J hJ hγM hsrc 0 1 zero_lt_one hunit (ContinuousLinearMap.id ℝ _)
  have hsub : Ioo (-δ) (1 + δ) ⊆ J := by
    intro t ht
    exact (hsol t (by simpa only [zero_sub] using ht)).1
  refine ⟨δ, hδ, W, hW0, ?_, hsub, ?_⟩
  · simpa only [zero_sub] using hW
  · intro t ht
    obtain ⟨_, hder, hp⟩ := hsol t (by simpa only [zero_sub] using ht)
    refine ⟨?_, ?_⟩
    · simpa only [chartParallelCoefficient, euclidean_chartPt] using hder
    · intro v w
      simpa only [euclidean_chartPt, ContinuousLinearMap.id_apply] using hp v w

end Yau.Proofs.C03Aux
