import Yau.Proofs.F01AActualScalarTimeCap
import Yau.Proofs.F01AInterfaces
import Yau.Proofs.F01ApproximatingScalarInitial
import Yau.Proofs.F01ControlledConformalBounds
import Yau.Proofs.F01ControlledBackground
import Yau.Proofs.F01ConformalCompactSublevels

/-! One scalar coefficient precedes the approximation level and every
actual continued solution. Its finite global boundedness inlet is proved
from that solution's native PDE and finite coarse metric sandwich. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem controlled_native_scalar_caps
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ a0 : ℝ, 0 < a0 ∧ ∀ (L : ℝ) (ho : u o < L),
      let N := sublevelManifold X.manifold u hu.1 o L ho
      let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
      ∀ (T : ℝ) (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
        0 < T → NativePotentialSlab α T h U → ∀ x t, t ∈ Icc 0 T →
          flowLogDetTime α h (Icc 0 T) x t ≤ a0 / L ^ 2 ∧
          flowLogDetRatio α h x t ≤ (a0 / L ^ 2) * t ∧
          U x t ≤ (a0 / L ^ 2) * t ^ 2 / 2 := by
  obtain ⟨a0, ha0, hInitial⟩ := controlled_approximating_negative_scalar_initial X o u hu
  obtain ⟨Af, hAf, Bf, hBf, hfbounds⟩ := controlled_conformal_gradient_levi X o u hu
  refine ⟨a0, ha0, ?_⟩
  intro L ho
  dsimp only
  intro T h U hT hslab
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let f : N.Carrier → ℝ := approximatingScalar X.manifold u hu.1 o L ho
  have hL : 0 < L := (zero_lt_one.trans_le (hu.2.2.1 o)).trans ho
  obtain ⟨hα, hBG, _⟩ := controlled_background_geometry X o u hu ho
  obtain ⟨A⟩ := exists_boundedChartFamily α hBG
  rcases hslab with ⟨hh0, hh, hU, hU0, C, hC, hdata⟩
  have hf : SmoothFn f := approximatingScalar_smoothFn u hu.1 o hL ho
  have hf0 (x : N.Carrier) : 0 ≤ f x :=
    conformalProfile_nonneg ((div_lt_one hL).mpr
      (sublevelManifold_point_level X.manifold u hu.1 o L ho x))
  have hproper : ∀ b : ℝ, IsCompact {x : N.Carrier | f x ≤ b} :=
    conformalProfile_compact_component_sublevel u (continuous_of_smoothFn hu.1) hu.2.1 o hL
  exact native_scalar_cap_and_potential_upper α hα A h U hT hC hh hU hh0 hU0
    (fun t ht x => (hdata x t ht).2.2.1)
    (fun x t ht => (hdata x t ht).2.2.2)
    (fun x t ht => ⟨(hdata x t ht).1, (hdata x t ht).2.1⟩)
    (hInitial L ho) f hf hf0 hproper (div_nonneg hBf.le (sq_nonneg L))
    (fun x => (hfbounds L ho x).2.2)

end Yau.NodeProofs.F01Aux
