import Yau.Proofs.V02FlowCoordinates

/-! Genuine fixed-chart vector fields and their actual differential cocycle. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

def cotangentVectorOfCoordsLinear : (CotangentIndex n → ℂ) →ₗ[ℂ] CotangentCoord n where
  toFun := cotangentVectorOfCoords
  map_add' v w := by ext i <;> rfl
  map_smul' c v := by ext i <;> rfl

def cotangentVectorOfCoordsCLM : (CotangentIndex n → ℂ) →L[ℂ] CotangentCoord n :=
  (cotangentVectorOfCoordsLinear (n := n)).toContinuousLinearMap

def cotangentChartField (Z : CotangentPoint M → CotangentIndex n → ℂ) (x : M.Carrier)
    (z : CotangentCoord n) : CotangentCoord n :=
  cotangentVectorOfCoords
    (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
      Z (cotangentChartInv x z))

theorem cotangentChartField_differentiableOn
    {Z : CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z (cotangentChartInv x z)) i) (cotangentTarget x)) (x : M.Carrier) :
    DifferentiableOn ℂ (cotangentChartField Z x) (cotangentTarget x) := by
  exact (cotangentVectorOfCoordsCLM (n := n)).differentiable.comp_differentiableOn
    (differentiableOn_pi.mpr (hZ x))

theorem cotangentChartField_contDiffOn
    {Z : CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z (cotangentChartInv x z)) i) (cotangentTarget x)) (x : M.Carrier) :
    ContDiffOn ℂ ∞ (cotangentChartField Z x) (cotangentTarget x) :=
  complex_holomorphic_contDiffOn
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ)
    (cotangentChartField_differentiableOn hZ x)

theorem cotangentChartChange_fderiv_comp (x x' x'' : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x')
    (hy'' : y ∈ cotangentSource x'') :
    (fderiv ℂ (fun z => cotangentChart x'' (cotangentChartInv x' z))
      (cotangentChart x' y)).comp
      (fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z))
        (cotangentChart x y)) =
      fderiv ℂ (fun z => cotangentChart x'' (cotangentChartInv x z))
        (cotangentChart x y) := by
  let T : CotangentCoord n → CotangentCoord n :=
    fun z => cotangentChart x' (cotangentChartInv x z)
  let S : CotangentCoord n → CotangentCoord n :=
    fun z => cotangentChart x'' (cotangentChartInv x' z)
  have hz := cotangentChart_mapsTo x hy
  have hb : chartInv x (cotangentChart x y).1 = y.1 :=
    (extChartAt (ComplexModel n) x).left_inv hy
  have hb' : chartInv x' (cotangentChart x' y).1 = y.1 :=
    (extChartAt (ComplexModel n) x').left_inv hy'
  have hT := cotangentChartTransition_contDiffAt x x' hz (by rw [hb]; exact hy')
  have hS := cotangentChartTransition_contDiffAt x' x'' (cotangentChart_mapsTo x' hy')
    (by rw [hb']; exact hy'')
  have hTy : T (cotangentChart x y) = cotangentChart x' y := by
    dsimp [T]
    rw [cotangentChart_left_inv x hy]
  have heq : S ∘ T =ᶠ[𝓝 (cotangentChart x y)]
      (fun z => cotangentChart x'' (cotangentChartInv x z)) := by
    filter_upwards [(isOpen_cotangentChartOverlap x x').mem_nhds
      ⟨hz, by rw [hb]; exact hy'⟩] with z hz'
    exact congrArg (cotangentChart x'') (cotangentChart_left_inv x' hz'.2)
  have hcomp := fderiv_comp (cotangentChart x y)
    (hTy ▸ hS.differentiableAt (by simp)) (hT.differentiableAt (by simp))
  rw [heq.fderiv_eq] at hcomp
  simpa only [T, S, cotangentChart_left_inv x hy] using hcomp.symm

theorem cotangentChartChange_fderiv_self (x : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) :
    fderiv ℂ (fun z => cotangentChart x (cotangentChartInv x z)) (cotangentChart x y) =
      ContinuousLinearMap.id ℂ (CotangentCoord n) := by
  have heq : (fun z => cotangentChart x (cotangentChartInv x z)) =ᶠ[𝓝 (cotangentChart x y)] id := by
    filter_upwards [((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ).mem_nhds
      (cotangentChart_mapsTo x hy)] with z hz
    exact cotangentChart_right_inv x hz
  simpa only [fderiv_id] using heq.fderiv_eq (𝕜 := ℂ)

theorem cotangentChartField_at_chart (Z : CotangentPoint M → CotangentIndex n → ℂ)
    (x : M.Carrier) (y : CotangentPoint M) (hy : y ∈ cotangentSource x) :
    cotangentChartField Z x (cotangentChart x y) =
      fderiv ℂ (fun z => cotangentChart x (cotangentChartInv y.1 z))
        (cotangentChart y.1 y) (cotangentVectorOfCoords (Z y)) := by
  have hb : chartInv x (cotangentChart x y).1 = y.1 :=
    (extChartAt (ComplexModel n) x).left_inv hy
  simp only [cotangentChartField, hb, cotangentChart_left_inv x hy,
    cotangentTransition_mulVec]

theorem cotangentChartField_centered (Z : CotangentPoint M → CotangentIndex n → ℂ)
    (y : CotangentPoint M) :
    cotangentChartField Z y.1 (cotangentChart y.1 y) = cotangentVectorOfCoords (Z y) := by
  rw [cotangentChartField_at_chart Z y.1 y (mem_extChartAt_source _),
    cotangentChartChange_fderiv_self y.1 y (mem_extChartAt_source _)]
  rfl

theorem cotangentChartField_transport (Z : CotangentPoint M → CotangentIndex n → ℂ)
    (x x' : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') :
    fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z)) (cotangentChart x y)
      (cotangentChartField Z x (cotangentChart x y)) =
      cotangentChartField Z x' (cotangentChart x' y) := by
  rw [cotangentChartField_at_chart Z x y hy, cotangentChartField_at_chart Z x' y hy']
  exact congrArg (fun A : CotangentCoord n →L[ℂ] CotangentCoord n =>
    A (cotangentVectorOfCoords (Z y)))
    (cotangentChartChange_fderiv_comp y.1 x x' y (mem_extChartAt_source _) hy hy')

end Yau.Blueprint.V02FlowProof
