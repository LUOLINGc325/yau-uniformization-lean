import Yau.Proofs.P06HodgeRegularityCoefficients
import Yau.Proofs.P06HodgeRegularityNondivergence
import Yau.Proofs.P06HodgeRegularityCoreApprox

/-! Smooth compact chart extensions solve the actual forward Hodge system
on the region where their fixed cutoffs equal one. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03

section Germ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem regularityDirection_germ {u w : E → ℝ} {z : E}
    (h : u =ᶠ[𝓝 z] w) (e : E) : regularityDirection e u =ᶠ[𝓝 z] regularityDirection e w :=
  h.fderiv.mono fun _ hd => congrArg (fun L : E →L[ℝ] ℝ => L e) hd

end Germ

variable {n k : ℕ} {M : ComplexManifold n}

def hodgeRegularityChartInput {α : Type*} [Fintype α]
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (σ : ComplexVector n → ℝ) (A : RealForm M k) (z : ComplexVector n) (c : α) : ℝ :=
  σ z * hodgeRegularityCoord b A x z c

theorem hodgeRegularityChartInput_contDiff {α : Type*} [Fintype α]
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (σ : ComplexVector n → ℝ) (hσ : ContDiff ℝ ∞ σ) (hcσ : HasCompactSupport σ)
    (hσO : tsupport σ ⊆ chartTarget x) (A : RealForm M k) (hA : SmoothRealForm A) (c : α) :
    ContDiff ℝ ∞ (fun z => hodgeRegularityChartInput x b σ A z c) :=
  (scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
    σ hσ hcσ hσO _ (hodgeRegularityCoord_contDiffOn b A hA x c)).1

theorem hodgeRegularityChartInput_support {α : Type*} [Fintype α]
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (σ : ComplexVector n → ℝ) (A : RealForm M k) (c : α) :
    tsupport (fun z => hodgeRegularityChartInput x b σ A z c) ⊆ tsupport σ :=
  tsupport_mul_subset_left

/-- The coefficients and section are extended by fixed compact cutoffs;
on their plateau the computed Euclidean PDE is exactly the original Hodge
expression in every degree and every chart. -/
theorem hodgeRegularity_chart_cutoff_source {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (θ σ : ComplexVector n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ) (hθO : tsupport θ ⊆ chartTarget x)
    (hσ : ContDiff ℝ ∞ σ) (hcσ : HasCompactSupport σ) (hσO : tsupport σ ⊆ chartTarget x)
    {V : Set (ComplexVector n)} (hV : IsOpen V) (hVO : V ⊆ chartTarget x)
    (hθone : ∀ z ∈ V, θ z = 1) (hσone : ∀ z ∈ V, σ z = 1)
    (A : RealForm M k) (hA : SmoothRealForm A) {z : ComplexVector n} (hz : z ∈ V) (r : α) :
    regularityScalarSystem (realModelBasis n)
      (fun i j y => θ y * hodgeRegularityQ g.form x i j y)
      (regularityScalarBeta (realModelBasis n)
        (fun i j y => θ y * hodgeRegularityQ g.form x i j y)
        (fun r c i y => θ y * hodgeRegularityE1 g.form x b r c i y))
      (fun r c y => θ y * hodgeRegularityE0 g.form x b r c y)
      (hodgeRegularityChartInput x b σ A) z r =
      hodgeRegularityCoord b (hodgeRealForm g.form k A) x z r := by
  classical
  have hq (i j : RIdx n) : ContDiff ℝ ∞ (fun y => θ y * hodgeRegularityQ g.form x i j y) :=
    (scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
      θ hθ hcθ hθO _ (hodgeRegularityQ_contDiffOn g x i j)).1
  have he1 (r c : α) (i : RIdx n) :
      ContDiff ℝ ∞ (fun y => θ y * hodgeRegularityE1 g.form x b r c i y) :=
    (scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
      θ hθ hcθ hθO _ (hodgeRegularityE1_contDiffOn g x b r c i)).1
  have hU (c : α) : ContDiff ℝ ∞ (fun y => hodgeRegularityChartInput x b σ A y c) :=
    hodgeRegularityChartInput_contDiff x b σ hσ hcσ hσO A hA c
  rw [regularityScalarSystem_nondivergence _ _ _ _ _ hq he1 hU,
    hodgeRegularity_chart_system g μ hμ A hA x b (hVO hz) r]
  have hvalue (c : α) : (fun y => hodgeRegularityChartInput x b σ A y c) =ᶠ[𝓝 z]
      fun y => hodgeRegularityCoord b A x y c := by
    filter_upwards [hV.mem_nhds hz] with y hy
    simp only [hodgeRegularityChartInput, hσone y hy, one_mul]
  have hfirst (i : RIdx n) (c : α) :
      regularityDirection (realModelBasis n i) (fun y => hodgeRegularityChartInput x b σ A y c) z =
        regularityDirection (realModelBasis n i) (fun y => hodgeRegularityCoord b A x y c) z :=
    (regularityDirection_germ (hvalue c) (realModelBasis n i)).eq_of_nhds
  have hsecond (i j : RIdx n) :
      regularityDirection (realModelBasis n i)
        (regularityDirection (realModelBasis n j) (fun y => hodgeRegularityChartInput x b σ A y r)) z =
      regularityDirection (realModelBasis n i)
        (regularityDirection (realModelBasis n j) (fun y => hodgeRegularityCoord b A x y r)) z :=
    (regularityDirection_germ
      (regularityDirection_germ (hvalue r) (realModelBasis n j)) (realModelBasis n i)).eq_of_nhds
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hθone z hz, one_mul, hsecond]
      rfl
    · apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      rw [hθone z hz, one_mul, hfirst]
  · apply Finset.sum_congr rfl
    intro c _
    rw [hθone z hz, one_mul, (hvalue c).eq_of_nhds]

end Yau.NodeProofs.P06Aux
