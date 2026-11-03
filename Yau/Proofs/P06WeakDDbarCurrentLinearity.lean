import Yau.Proofs.P06WeakDDbarCurrentAdjoint

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def smoothCodifferentialLinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    smoothFormSubmodule (M := M) (k + 1) →ₗ[ℝ] smoothFormSubmodule (M := M) k where
  toFun A := ⟨codifferentialRealForm g.form A.val,
    codifferentialRealForm_smooth g μ hμ A.val A.property⟩
  map_add' A B := Subtype.ext (codifferentialRealForm_add g μ hμ A.val B.val A.property B.property)
  map_smul' r A := Subtype.ext (codifferentialRealForm_smul g μ hμ r A.val A.property)

def smoothJPullbackOneLinear :
    smoothFormSubmodule (M := M) 1 →ₗ[ℝ] smoothFormSubmodule (M := M) 1 where
  toFun A := ⟨jPullbackForm A.val, jPullbackOne_smooth A.val A.property⟩
  map_add' A B := by
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.ext
    intro V
    simp [jPullbackForm]
  map_smul' r A := by
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.ext
    intro V
    simp [jPullbackForm]

def smoothScalarValueLinear : smoothFormSubmodule (M := M) 0 →ₗ[ℝ] (M.Carrier → ℝ) where
  toFun A := scalarValue A.val
  map_add' A B := by funext x; rfl
  map_smul' r A := by funext x; rfl

def ddAdjointSmoothLinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    smoothFormSubmodule (M := M) 2 →ₗ[ℝ] (M.Carrier → ℝ) :=
  (1 / 2 : ℝ) • smoothScalarValueLinear.comp
    ((smoothCodifferentialLinear g μ hμ 0).comp
      (smoothJPullbackOneLinear.comp (smoothCodifferentialLinear g μ hμ 1)))

theorem ddAdjointSmoothLinear_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : smoothFormSubmodule (M := M) 2) :
    ddAdjointSmoothLinear g μ hμ B = ddAdjointScalar g.form B.val := rfl

/-- The actual δJ*δ expression distributes over finite sums of smooth forms. -/
theorem ddAdjointScalar_fintypeSum {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (B : ι → RealForm M 2) (hB : ∀ i, SmoothRealForm (B i)) :
    ddAdjointScalar g.form (∑ i, B i) = ∑ i, ddAdjointScalar g.form (B i) := by
  let U : ι → smoothFormSubmodule (M := M) 2 := fun i => ⟨B i, hB i⟩
  have he := map_sum (ddAdjointSmoothLinear g μ hμ) U Finset.univ
  simp only [ddAdjointSmoothLinear_apply] at he
  simpa only [Submodule.coe_sum, U] using he

end Yau.NodeProofs.P06Aux.WeakCurrent
