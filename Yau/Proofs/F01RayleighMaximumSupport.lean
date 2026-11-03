import Yau.Proofs.F01MetricRayleighPositive
import Yau.Proofs.F01RayleighPenalty

/-! A genuine maximum of the largest-eigenvalue scalar gives spatial and
temporal maxima for its actual fixed-coordinate Rayleigh lower support. -/
noncomputable section
open Set Filter
open scoped Topology Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def metricRayleighPenalty (α : HermitianField M) (h : ℝ → HermitianField M)
    (Q : ℝ → M.Carrier → ℝ) (f : M.Carrier → ℝ) (a δ : ℝ) (p : M.Carrier × ℝ) : ℝ :=
  Real.log (metricLargestRayleigh α (h p.2) p.1) - rayleighPenalty a (Q p.2 p.1) - δ * f p.1

def chartRayleighPenalty (α : HermitianField M) (h : ℝ → HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (j : Fin n)
    (Q : ℝ → M.Carrier → ℝ) (f : M.Carrier → ℝ) (a δ : ℝ) (p : ComplexVector n × ℝ) : ℝ :=
  Real.log (matrixRayleigh (pullbackMatrix α e p.1) (pullbackMatrix (h p.2) e p.1)
    (Pi.single j 1)) - rayleighPenalty a (Q p.2 (e p.1)) - δ * f (e p.1)

theorem chartRayleighPenalty_le_metric (α : HermitianField M) (h : ℝ → HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (j : Fin n) (Q : ℝ → M.Carrier → ℝ) (f : M.Carrier → ℝ) (a δ t : ℝ)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    chartRayleighPenalty α h e j Q f a δ (z, t) ≤
      metricRayleighPenalty α h Q f a δ (e z, t) := by
  have hv : (Pi.single j (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
    intro hh
    have hi := congrFun hh j
    simpa using hi
  have hpos : 0 < matrixRayleigh (pullbackMatrix α e z) (pullbackMatrix (h t) e z)
      (Pi.single j 1) := div_pos
    (matrixQuadraticValue_pos (pullbackMatrix_posDef (h t) e he hei hz) hv)
    (matrixQuadraticValue_pos (pullbackMatrix_posDef α e he hei hz) hv)
  have hlog := Real.log_le_log hpos (fixed_chart_rayleigh_le_largest α (h t) e he hei hz _)
  exact sub_le_sub_right (sub_le_sub_right hlog _) _

theorem actual_rayleigh_support_at_max
    (α : HermitianField M) (h : ℝ → HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs : (0 : ComplexVector n) ∈ e.source) (j : Fin n)
    (Q : ℝ → M.Carrier → ℝ) (f : M.Carrier → ℝ) (a δ t : ℝ) (I : Set ℝ) (ht : t ∈ I)
    (hcontact : matrixRayleigh (pullbackMatrix α e 0) (pullbackMatrix (h t) e 0)
      (Pi.single j 1) = metricLargestRayleigh α (h t) (e 0))
    (hmax : IsMaxOn (metricRayleighPenalty α h Q f a δ) (univ ×ˢ I) (e 0, t)) :
    IsLocalMax (fun w => chartRayleighPenalty α h e j Q f a δ (w, t)) 0 ∧
      IsMaxOn (fun s => chartRayleighPenalty α h e j Q f a δ (0, s)) I t := by
  have heq : chartRayleighPenalty α h e j Q f a δ (0, t) =
      metricRayleighPenalty α h Q f a δ (e 0, t) := by
    unfold chartRayleighPenalty metricRayleighPenalty
    rw [hcontact]
  constructor
  · change ∀ᶠ w in 𝓝 0, chartRayleighPenalty α h e j Q f a δ (w, t) ≤
      chartRayleighPenalty α h e j Q f a δ (0, t)
    filter_upwards [e.open_source.mem_nhds hs] with w hw
    rw [heq]
    exact (chartRayleighPenalty_le_metric α h e he hei j Q f a δ t hw).trans
      (hmax (show (e w, t) ∈ univ ×ˢ I from ⟨mem_univ _, ht⟩))
  · intro s hsI
    change chartRayleighPenalty α h e j Q f a δ (0, s) ≤
      chartRayleighPenalty α h e j Q f a δ (0, t)
    rw [heq]
    exact (chartRayleighPenalty_le_metric α h e he hei j Q f a δ s hs).trans
      (hmax (show (e 0, s) ∈ univ ×ˢ I from ⟨mem_univ _, hsI⟩))

end Yau.NodeProofs.F01Aux
