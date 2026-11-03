import Yau.Proofs.D05CotangentBlock

/-! The actual induced cotangent atlas preserves the canonical complex
bivector. The Hessian term is retained through the explicit local model. -/

open scoped Manifold Topology ContDiff Matrix
open Filter

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentChartTransition_eventuallyEq_model (x x' : M.Carrier)
    {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hy' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) :
    (fun w => cotangentChart x' (cotangentChartInv x w)) =ᶠ[𝓝 z]
      modelCotangentChange (fun v => chartPt x' (chartInv x v))
        (fun v => chartPt x (chartInv x' v)) := by
  have hInvSmooth : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (chartInv x) z.1 :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) x).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz.1)
  have hInv : ContinuousAt (fun w : CotangentCoord n => chartInv x w.1) z :=
    hInvSmooth.continuousAt.comp continuousAt_fst
  have htarget : ∀ᶠ w in 𝓝 z, w ∈ cotangentTarget x :=
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ).mem_nhds hz
  have hsource : ∀ᶠ w in 𝓝 z,
      chartInv x w.1 ∈ (extChartAt (ComplexModel n) x').source :=
    hInv.eventually ((isOpen_extChartAt_source (I := ComplexModel n) x').mem_nhds hy')
  filter_upwards [htarget, hsource] with w hw hw'
  apply Prod.ext
  · rfl
  ext i
  have hDw : fderiv ℂ (fun v => chartPt x (chartInv x' v))
      (chartPt x' (chartInv x w.1)) =
      tangentCoordChange (ComplexModel n) x' x (chartInv x w.1) := by
    have hroundw : chartInv x' (chartPt x' (chartInv x w.1)) = chartInv x w.1 :=
      (extChartAt (ComplexModel n) x').left_inv hw'
    calc
      _ = tangentCoordChange (ComplexModel n) x' x
          (chartInv x' (chartPt x' (chartInv x w.1))) :=
        chartTransition_fderiv_eq_coordChange x' x
          ((extChartAt (ComplexModel n) x').map_source hw')
      _ = _ := by rw [hroundw]
  change (cotangentChart x' (cotangentChartInv x w)).2 i =
    ∑ k, (fderiv ℂ (fun v => chartPt x (chartInv x' v))
      (chartPt x' (chartInv x w.1)) (stdVec i)) k * w.2 k
  rw [cotangentChart_transition_fiber x x' hw hw', hDw]

theorem cotangentTransition_symplectic (x x' : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') :
    cotangentTransition x x' y * canonicalBivector * (cotangentTransition x x' y)ᵀ =
      (canonicalBivector : CotangentMatrix n) := by
  let z := cotangentChart x y
  let φ : ComplexVector n → ComplexVector n := fun v => chartPt x' (chartInv x v)
  let ψ : ComplexVector n → ComplexVector n := fun v => chartPt x (chartInv x' v)
  have hz : z ∈ cotangentTarget x := cotangentChart_mapsTo x hy
  have hbase : chartInv x z.1 = y.1 := (extChartAt (ComplexModel n) x).left_inv hy
  have hφz : φ z.1 = chartPt x' y.1 := by dsimp only [φ]; rw [hbase]
  have hψbase : chartInv x' (φ z.1) = y.1 := by
    rw [hφz]
    exact (extChartAt (ComplexModel n) x').left_inv hy'
  have hs' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source := by
    rw [hbase]; exact hy'
  have hφ : ContDiffAt ℂ ∞ φ z.1 := chartTransition_contDiffAt x x' hz.1 hs'
  have hψ : ContDiffAt ℂ ∞ ψ (φ z.1) := by
    apply chartTransition_contDiffAt x' x
    · rw [hφz]; exact (extChartAt (ComplexModel n) x').map_source hy'
    · rw [hψbase]; exact hy
  have hDφ : fderiv ℂ φ z.1 = tangentCoordChange (ComplexModel n) x x' y.1 := by
    rw [chartTransition_fderiv_eq_coordChange x x' hz.1, hbase]
  have hDψ : fderiv ℂ ψ (φ z.1) = tangentCoordChange (ComplexModel n) x' x y.1 := by
    rw [chartTransition_fderiv_eq_coordChange x' x
      (by rw [hφz]; exact (extChartAt (ComplexModel n) x').map_source hy'), hψbase]
  have hinv : (fderiv ℂ φ z.1).comp (fderiv ℂ ψ (φ z.1)) =
      ContinuousLinearMap.id ℂ _ := by
    rw [hDφ, hDψ]
    apply ContinuousLinearMap.ext
    intro v
    change tangentCoordChange (ComplexModel n) x x' y.1
      (tangentCoordChange (ComplexModel n) x' x y.1 v) = v
    rw [tangentCoordChange_comp ⟨⟨hy', hy⟩, hy'⟩, tangentCoordChange_self hy']
  have heq := cotangentChartTransition_eventuallyEq_model x x' hz hs'
  have hT : cotangentTransition x x' y = cotangentModelJacobian φ ψ z := by
    ext i j
    change cotangentCoordsVector
      (fderiv ℂ (fun w => cotangentChart x' (cotangentChartInv x w)) z
        (cotangentDir j)) i = _
    rw [heq.fderiv_eq]
    rfl
  rw [hT]
  exact cotangentModelJacobian_symplectic hφ hψ hinv

end Yau.Blueprint.D05Proof
