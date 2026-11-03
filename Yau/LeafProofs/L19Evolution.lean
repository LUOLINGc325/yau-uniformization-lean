import Yau.LeafProofs.L19Regularity

/-! Time evolution of the actual gradient energies for a fixed metric. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The physical gradient pairing differentiates in time by its two
ordinary Leibniz terms. -/
theorem scalarGradientPair_time_hasDerivAt (h : HermitianField M)
    {u v : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (hv : SmoothSpaceTime v (Set.Ioi 0))
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => scalarGradientPair h (fun y => u y s) (fun y => v y s) x)
      (scalarGradientPair h (fun y => deriv (u y) t) (fun y => v y t) x +
        scalarGradientPair h (fun y => u y t) (fun y => deriv (v y) t) x) t := by
  let z := chartPt x x
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn h x z)⁻¹
  let U : RIdx n → ℝ → ℝ := fun i s => rDeriv (inChart x (fun y => u y s)) z i
  let V : RIdx n → ℝ → ℝ := fun i s => rDeriv (inChart x (fun y => v y s)) z i
  let DU : RIdx n → ℝ := fun i => rDeriv (inChart x (fun y => deriv (u y) t)) z i
  let DV : RIdx n → ℝ := fun i => rDeriv (inChart x (fun y => deriv (v y) t)) z i
  have hDU (i : RIdx n) : HasDerivAt (U i) (DU i) t :=
    smoothSpaceTime_spatial_time_hasDerivAt hu x (mem_extChartAt_target x) ht i
  have hDV (i : RIdx n) : HasDerivAt (V i) (DV i) t :=
    smoothSpaceTime_spatial_time_hasDerivAt hv x (mem_extChartAt_target x) ht i
  have hsum : HasDerivAt (fun s => ∑ i, ∑ j, A i j * U i s * V j s)
      (∑ i, ∑ j, (A i j * DU i * V j t + A i j * U i t * DV j)) t := by
    have hinner (i : RIdx n) : HasDerivAt (fun s => ∑ j, A i j * U i s * V j s)
        (∑ j, (A i j * DU i * V j t + A i j * U i t * DV j)) t := by
      simpa only [Finset.sum_fn, Pi.mul_apply] using HasDerivAt.sum (u := Finset.univ)
        (fun j _ => ((hDU i).const_mul (A i j)).mul (hDV j))
    simpa only [Finset.sum_fn] using HasDerivAt.sum (u := Finset.univ)
      (fun i _ => hinner i)
  have hfunction : (fun s => scalarGradientPair h (fun y => u y s) (fun y => v y s) x) =
      (fun s => ∑ i, ∑ j, A i j * U i s * V j s) := by
    funext s
    exact chartGradientPair_eq_sum h x (inChart x (fun y => u y s))
      (inChart x (fun y => v y s)) z
  rw [hfunction]
  convert hsum using 1
  simp only [scalarGradientPair, chartGradientPair_eq_sum, Finset.sum_add_distrib,
    A, U, V, DU, DV, z]

theorem scalarGradientPair_self_time_hasDerivAt (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => scalarGradientPair h (fun y => u y s) (fun y => u y s) x)
      (2 * scalarGradientPair h (fun y => u y t) (fun y => deriv (u y) t) x) t := by
  have hd := scalarGradientPair_time_hasDerivAt h hu hu x ht
  rw [scalarGradientPair_symm h (fun y => deriv (u y) t) (fun y => u y t) x] at hd
  convert hd using 1
  ring

/-- The time derivative of the project's half-real energy has exactly one
physical pairing term; the factor is fixed by the genuine normalization. -/
theorem gradNormSq_time_hasDerivAt (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => gradNormSq h (fun y => u y s) x)
      (scalarGradientPair h (fun y => u y t) (fun y => deriv (u y) t) x) t := by
  have hd := (scalarGradientPair_self_time_hasDerivAt h hu x ht).div_const 2
  have hd' : HasDerivAt
      (fun s => scalarGradientPair h (fun y => u y s) (fun y => u y s) x / 2)
      (scalarGradientPair h (fun y => u y t) (fun y => deriv (u y) t) x) t := by
    convert hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [scalarGradientPair_eq_twice_gradNormSq h (smoothSpaceTime_slice hu hs) x]
  ring

end Yau.LeafProofs.L19Aux
