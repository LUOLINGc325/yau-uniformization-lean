import Yau.Proofs.C03ShortLiftMapSpeed

/-! Actual source curves yield the forward distance comparison with their exact lengths. -/
noncomputable section
open scoped Manifold Topology ContDiff
open Set MeasureTheory
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

local instance (hn : 1 ≤ n) : NormedAddCommGroup (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℝ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℂ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))

def mappedIntegrableCurve {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn))
    (k : HermitianField M)
    (heq : ∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
      (ks z).toFun u v = (k (Phi z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z v))
    {a b : ComplexVector n} (gamma : IntegrableCurve ks a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma.1 t : ComplexVector n) ∈ Metric.ball 0 r) :
    IntegrableCurve k (Phi a) (Phi b) :=
  ⟨mappedCurve hPhi hn gamma.1 hmem,
    gamma.2.congr (mappedCurve_speed_ae hPhi hn ks k heq gamma.1 hmem).symm⟩

theorem forward_curve_length_bound {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn))
    (k : HermitianField M)
    (heq : ∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
      (ks z).toFun u v = (k (Phi z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z v))
    {a b : ComplexVector n} (gamma : IntegrableCurve ks a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma.1 t : ComplexVector n) ∈ Metric.ball 0 r) :
    inducedDistance k (Phi a) (Phi b) ≤ curveLength ks gamma.1 := by
  have H := inducedDistance_le_curveLength k (mappedIntegrableCurve hPhi hn ks k heq gamma hmem)
  change inducedDistance k (Phi a) (Phi b) ≤
    curveLength k (mappedCurve hPhi hn gamma.1 hmem) at H
  rw [mappedCurve_length_eq hPhi hn ks k heq gamma.1 hmem] at H
  exact H

theorem forward_distance_of_minimizing_curve {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn))
    (k : HermitianField M)
    (heq : ∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
      (ks z).toFun u v = (k (Phi z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z v))
    {a b : ComplexVector n} (gamma : IntegrableCurve ks a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma.1 t : ComplexVector n) ∈ Metric.ball 0 r)
    (hmin : curveLength ks gamma.1 = inducedDistance ks a b) :
    inducedDistance k (Phi a) (Phi b) ≤ inducedDistance ks a b :=
  (forward_curve_length_bound hPhi hn ks k heq gamma hmem).trans_eq hmin

end Yau.Proofs.C03Aux.ShortLift

