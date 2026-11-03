import Yau.Proofs.F04EnergyRepresentatives

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarL2_add {μ : Measure M.Carrier} {f v : M.Carrier → ℝ}
    (hf : ScalarL2 μ f) (hv : ScalarL2 μ v) : ScalarL2 μ (f + v) :=
  (scalarL2_iff_memLp _ _).mpr (((scalarL2_iff_memLp _ _).mp hf).add
    ((scalarL2_iff_memLp _ _).mp hv))

theorem scalarL2_smul {μ : Measure M.Carrier} {f : M.Carrier → ℝ}
    (hf : ScalarL2 μ f) (c : ℝ) : ScalarL2 μ (c • f) :=
  (scalarL2_iff_memLp _ _).mpr (((scalarL2_iff_memLp _ _).mp hf).const_smul c)

theorem scalarToLp_add {μ : Measure M.Carrier} {f v : M.Carrier → ℝ}
    (hf : ScalarL2 μ f) (hv : ScalarL2 μ v) (hfv : ScalarL2 μ (f + v)) :
    scalarToLp hfv = scalarToLp hf + scalarToLp hv := by
  apply Lp.ext
  filter_upwards [scalarToLp_coe hfv, scalarToLp_coe hf, scalarToLp_coe hv,
    Lp.coeFn_add (scalarToLp hf) (scalarToLp hv)] with x hs hf hv hc
  rw [hs, hc]
  simp only [Pi.add_apply, hf, hv]

theorem scalarToLp_smul {μ : Measure M.Carrier} {f : M.Carrier → ℝ}
    (hf : ScalarL2 μ f) (c : ℝ) (hcf : ScalarL2 μ (c • f)) :
    scalarToLp hcf = c • scalarToLp hf := by
  apply Lp.ext
  filter_upwards [scalarToLp_coe hcf, scalarToLp_coe hf,
    Lp.coeFn_smul c (scalarToLp hf)] with x hs hf hc
  rw [hs, hc]
  simp only [Pi.smul_apply, hf]

theorem realize_section_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    {k : ℕ} (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B)
    (hAB : L2RealForm g.form μ (A + B)) :
    realizeL2Form g μ (L2FormSpace.ofSection (A + B) hAB) =
      realizeL2Form g μ (L2FormSpace.ofSection A hA) +
        realizeL2Form g μ (L2FormSpace.ofSection B hB) := by
  simp only [realizeL2Form]
  rw [← UniformSpace.Completion.coe_add]
  congr 1

theorem realize_section_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    {k : ℕ} (c : ℝ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hcA : L2RealForm g.form μ (c • A)) :
    realizeL2Form g μ (L2FormSpace.ofSection (c • A) hcA) =
      c • realizeL2Form g μ (L2FormSpace.ofSection A hA) := by
  simp only [realizeL2Form]
  rw [← UniformSpace.Completion.coe_smul]
  congr 1

end Yau.F04Proof
