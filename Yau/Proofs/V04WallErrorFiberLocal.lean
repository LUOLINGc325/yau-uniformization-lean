import Yau.Proofs.V04WallErrorFiberScaling

/-! Local regularity at positive walls, without assuming reciprocal walls
are smooth away from their actual positive region. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem spatial_slice_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsOpen S) {J : Set ℝ} {f : E × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ J)) {z : E} (hz : z ∈ S) {t : ℝ} (ht : t ∈ J) :
    ContDiffAt ℝ ∞ (fun w => f (w, t)) z := by
  have hs := hf.comp ((contDiff_id.prodMk contDiff_const).contDiffOn)
    (fun w hw => ⟨hw, ht⟩)
  exact hs.contDiffAt (hS.mem_nhds hz)

theorem fiberNormModel_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) :
    ContDiffAt ℝ ∞ (fiberNormModel d x t) z := by
  exact spatial_slice_contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ)
    (fiberNormModel_contDiffOn hd x) hz ht

theorem fiberBaseModel_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) :
    ContDiffAt ℝ ∞ (fiberBaseModel d j x t) z := by
  exact spatial_slice_contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ)
    (fiberBaseModel_contDiffOn hd j x) hz ht

theorem fiberBaseWallModel_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hδ : deltaBase d j (cotangentChartInv x z).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fiberBaseWallModel d j x) z := by
  have hOp : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact (((deltaBase_chart_contDiffOn hd j x).contDiffAt (hOp.mem_nhds hz)).inv hδ).sub contDiffAt_const

theorem normalizedFiberWall_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hε : normalizedFiberProfile d x z ≠ 0) :
    ContDiffAt ℝ ∞ (normalizedFiberWall d x) z := by
  have hOp : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact (((normalizedFiberProfile_contDiffOn hd x).contDiffAt (hOp.mem_nhds hz)).inv hε).sub contDiffAt_const

theorem updatedFiberWall_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) (b : ℝ) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hε : deltaFiber {d with B := Function.update d.B j b} j (cotangentChartInv x z) ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => wallFiber {d with B := Function.update d.B j b} j
      (cotangentChartInv x w)) z := by
  have hN := fiberNormModel_contDiffAt hd x hz
    (show (0 : ℝ) ∈ Set.Icc 0 d.extendedT from ⟨le_rfl, (hd.1.trans hd.2.1).le⟩)
  have hP := (setup_wallProfiles hd).2.1.contDiffAt.comp z (hN.div_const (b ^ 2))
  have hPn : d.profileFiber (fiberNormModel d x 0 z / b ^ 2) ≠ 0 := by
    simpa only [deltaFiber, Function.update_self, fiberNormModel] using hε
  have hi := (hP.inv hPn).sub (contDiffAt_const (c := (1 : ℝ)))
  simp only [Function.comp_def, fiberNormModel] at hi
  simp only [wallFiber, deltaFiber, Function.update_self]
  convert! hi using 1

theorem clearedReciprocalMatrix_wall_real {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z)
    (hne : f z ≠ 0) (dir : ι → E) :
    clearedReciprocalMatrix f 3 dir z =
      f z ^ 3 • leviMatrix (fun w => (f w)⁻¹ - 1) z dir := by
  have hconst : leviMatrix (fun w => (f w)⁻¹ - 1) z dir =
      leviMatrix (fun w => (f w)⁻¹) z dir := by
    simpa only [sub_eq_add_neg] using leviMatrix_add_const (fun w => (f w)⁻¹) (-1) z dir
  rw [hconst, clearedReciprocalMatrix_eq hf hne dir le_rfl]
  ext a b
  simp only [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_pow, smul_eq_mul]

theorem fiberBaseCleared_eq {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hδ : deltaBase d j (cotangentChartInv x z).1 ≠ 0) :
    fiberBaseCleared d j x z = deltaBase d j (cotangentChartInv x z).1 ^ 3 •
      leviMatrix (fiberBaseWallModel d j x) z cotangentDir := by
  have hOp : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact clearedReciprocalMatrix_wall_real
    (((deltaBase_chart_contDiffOn hd j x).contDiffAt (hOp.mem_nhds hz)).of_le (by simp)) hδ cotangentDir

theorem fiberFiberCleared_eq {d : VariationData X q} (hd : VariationSetup d)
    (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hε : normalizedFiberProfile d x z ≠ 0) :
    fiberFiberCleared d x z = normalizedFiberProfile d x z ^ 3 •
      leviMatrix (normalizedFiberWall d x) z cotangentDir := by
  have hOp : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact clearedReciprocalMatrix_wall_real
    (((normalizedFiberProfile_contDiffOn hd x).contDiffAt (hOp.mem_nhds hz)).of_le (by simp)) hε cotangentDir

end Yau.Blueprint.V04Proof.WallErrorAux
