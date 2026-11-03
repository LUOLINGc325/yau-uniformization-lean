import Yau.Proofs.V03ClearedAmbientLogCovector
import Yau.Proofs.V03ClearedAmbientLogTensor
import Yau.Proofs.V03AmbientLeviContraction
import Yau.Proofs.V03BoundaryColumnField
import Yau.Proofs.V03NormalizedVelocityScalar
import Yau.Proofs.V03ActualLogFirstJet
import Yau.Proofs.V03RealWirtingerDifferential

/-! Exact contractions of the original first field with the genuine
cleared logarithmic covector and tensor. -/

open scoped Topology ContDiff Matrix Manifold ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem ambientLogCovector_boundary_contract {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (F : VariationDisc X)
    (hF : AdmissibleVariationDisc d j F) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (θ : ℝ) :
    let ζ := circlePoint θ
    let y := F.f ζ
    ambientLogCovector d j a y ⬝ᵥ boundaryColumnField d F E l θ =
      (wallPower d j a y : ℂ) * wirt (fun z =>
        (Real.log (wallProduct d j (cotangentChartInv y.1 z)) : ℂ))
        (cotangentChart y.1 y) (cotangentVectorOfCoords (E ζ *ᵥ l ζ)) := by
  let ζ := circlePoint θ
  let y := F.f ζ
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hround := cotangentChart_left_inv y.1 hself
  have hz := cotangentChart_mapsTo y.1 hself
  have hopen : IsOpen (cotangentTarget y.1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) y.1).prod isOpen_univ
  have hp : wallProduct d j y ≠ 0 := (admissible_wallProduct_bounds hd hF θ).1.ne'
  have hp' : wallProduct d j (cotangentChartInv y.1 (cotangentChart y.1 y)) ≠ 0 := by
    simpa only [hround] using hp
  have hclear := clearedLogCovector_eq
    (((wallProduct_chart_contDiffOn hd j y.1).contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp))
    hp' a (by omega : 1 ≤ a) cotangentDir
  rw [hround] at hclear
  change ambientCovector (cotangentDG d.G y.1 (cotangentChartInv y.1 (cotangentChart y.1 y)))
      (clearedLogCovector (fun w => wallProduct d j (cotangentChartInv y.1 w)) a cotangentDir
        (cotangentChart y.1 y)) ⬝ᵥ
      ((cotangentDG d.G y.1 y * E ζ) *ᵥ l ζ) = _
  rw [hround, hclear, ← Matrix.mulVec_mulVec,
    ambientCovector_contract (cotangentDG_gram_posDef hd.2.2.2.2.1 y).isUnit,
    smul_dotProduct, smul_eq_mul, ← cotangent_wirt_contraction]
  simp only [wallPower, Complex.ofReal_pow]
  rfl

theorem ambientLogTensor_boundary_contract {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (F : VariationDisc X)
    (hF : AdmissibleVariationDisc d j F) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (θ : ℝ) :
    let ζ := circlePoint θ
    let y := F.f ζ
    let V := cotangentVectorOfCoords (E ζ *ᵥ l ζ)
    star (boundaryColumnField d F E l θ) ⬝ᵥ
      (ambientLogTensor d j a y *ᵥ boundaryColumnField d F E l θ) =
      (wallPower d j a y : ℂ) ^ 2 *
        wirt (fun u => wirtBar (fun u' =>
          (Real.log (wallProduct d j (cotangentChartInv y.1 u')) : ℂ)) u V)
          (cotangentChart y.1 y) V := by
  let ζ := circlePoint θ
  let y := F.f ζ
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hround := cotangentChart_left_inv y.1 hself
  have hz := cotangentChart_mapsTo y.1 hself
  have hopen : IsOpen (cotangentTarget y.1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) y.1).prod isOpen_univ
  have hp : wallProduct d j y ≠ 0 := (admissible_wallProduct_bounds hd hF θ).1.ne'
  have hp' : wallProduct d j (cotangentChartInv y.1 (cotangentChart y.1 y)) ≠ 0 := by
    simpa only [hround] using hp
  have hclear := clearedLogMatrix_eq
    (((wallProduct_chart_contDiffOn hd j y.1).contDiffAt (hopen.mem_nhds hz)).of_le (by simp))
    hp' cotangentDir (by omega : 2 ≤ 2 * a)
  rw [hround] at hclear
  have hb := logWall_chart_contDiffAt hd j y.1 hself hp
  change star ((cotangentDG d.G y.1 y * E ζ) *ᵥ l ζ) ⬝ᵥ
    (ambientLeviTensor (cotangentDG d.G y.1 (cotangentChartInv y.1 (cotangentChart y.1 y)))
      (clearedLogMatrix (fun w => wallProduct d j (cotangentChartInv y.1 w)) (2 * a) cotangentDir
        (cotangentChart y.1 y)) *ᵥ ((cotangentDG d.G y.1 y * E ζ) *ᵥ l ζ)) = _
  rw [hround, hclear]
  simp only [← Matrix.mulVec_mulVec]
  rw [ambientLeviTensor_vectors (cotangentDG_gram_posDef hd.2.2.2.2.1 y).isUnit,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← cotangent_levi_contraction hb]
  have hpower : (wallPower d j a y : ℂ) ^ 2 = (wallProduct d j y : ℂ) ^ (2 * a) := by
    simp only [wallPower, Complex.ofReal_pow, ← pow_mul]
    congr 1
    omega
  rw [hpower]

theorem realized_logFirstJet_cleared {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (v : ℂ) (θ : ℝ) :
    realParameterDerivative (fun p : ℂ × ℝ => (logTrace d j (fz p.1) p.2 : ℂ)) v (0, θ) =
      (2 * (v * normalizedVelocityScalar d j a F h α θ *
        (ambientLogCovector d j a (F.f (circlePoint θ)) ⬝ᵥ boundaryColumnField d F E l θ)).re : ℝ) := by
  rw [realized_logTrace_realParameterDerivative hd j a F hF E l h α fz R hR v θ]
  have hb := logWall_chart_contDiffAt hd j (F.f (circlePoint θ)).1
    (mem_extChartAt_source (F.f (circlePoint θ)).1)
    (admissible_wallProduct_bounds hd hF θ).1.ne'
  rw [real_fderiv_eq_two_re_wirt (hb.differentiableAt (by norm_num)),
    cotangentVectorOfCoords_smul, wirt_smul_direction, wirt_smul_direction,
    ambientLogCovector_boundary_contract hd j a ha F hF E l θ]
  have hp := normalizedVelocityScalar_mul_power hd j a F hF h α θ
  rw [← hp]
  congr 2
  ring

end Yau.Blueprint.V03Proof
