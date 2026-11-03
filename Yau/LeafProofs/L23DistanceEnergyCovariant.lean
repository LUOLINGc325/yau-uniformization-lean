import Yau.LeafProofs.L23FieldMetricFirstVariation
import Yau.LeafProofs.L23CurvatureCalculus

/-! Actual coordinate covariant derivatives along a parameterized map. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def mapDirection (Z : E → V) (a : E) (p : E) : V := fderiv ℝ Z p a

def mapCovariantD (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z : E → V)
    (a : E) (W : E → V) (p : E) : V :=
  mapDirection W a p+Γ (Z p) (mapDirection Z a p) (W p)

def connectionCurvature (Γ : V → V →L[ℝ] V →L[ℝ] V) (z u v w : V) : V :=
  fderiv ℝ Γ z u v w-fderiv ℝ Γ z v u w+Γ z u (Γ z v w)-Γ z v (Γ z u w)

theorem mapDirection_hasFDerivAt (Z : E → V) {p : E} (hZ : ContDiffAt ℝ 2 Z p) (a : E) :
    HasFDerivAt (mapDirection Z a)
      ((fderiv ℝ (fderiv ℝ Z) p).flip a) p := by
  change HasFDerivAt (fun y => fderiv ℝ Z y a) ((fderiv ℝ (fderiv ℝ Z) p).flip a) p
  simpa only [mapDirection,ContinuousLinearMap.comp_zero,zero_add] using
    ((hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one).hasFDerivAt.clm_apply
      (hasFDerivAt_const a p)

theorem mapDirection_commute (Z : E → V) {p : E} (hZ : ContDiffAt ℝ 2 Z p) (a b : E) :
    mapDirection (mapDirection Z b) a p=mapDirection (mapDirection Z a) b p := by
  change fderiv ℝ (mapDirection Z b) p a=fderiv ℝ (mapDirection Z a) p b
  rw [(mapDirection_hasFDerivAt Z hZ b).fderiv,(mapDirection_hasFDerivAt Z hZ a).fderiv]
  exact hZ.isSymmSndFDerivAt (by norm_num) a b

theorem mapCovariantD_direction (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z W : E → V)
    {p : E} (hΓ : DifferentiableAt ℝ Γ (Z p)) (hZ : ContDiffAt ℝ 2 Z p)
    (hW : ContDiffAt ℝ 2 W p) (a b : E) :
    mapDirection (mapCovariantD Γ Z b W) a p=
      mapDirection (mapDirection W b) a p+
      fderiv ℝ Γ (Z p) (mapDirection Z a p) (mapDirection Z b p) (W p)+
      Γ (Z p) (mapDirection (mapDirection Z b) a p) (W p)+
      Γ (Z p) (mapDirection Z b p) (mapDirection W a p) := by
  have hD := (mapDirection_hasFDerivAt W hW b).add
    (((hΓ.hasFDerivAt.comp p (hZ.differentiableAt (by norm_num)).hasFDerivAt).clm_apply
      (mapDirection_hasFDerivAt Z hZ b)).clm_apply
      (hW.differentiableAt (by norm_num)).hasFDerivAt)
  have he := congrArg (fun L : E →L[ℝ] V => L a) hD.fderiv
  change mapDirection (mapCovariantD Γ Z b W) a p=_ at he
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at he
  rw [show (fderiv ℝ (fderiv ℝ W) p) a b=mapDirection (mapDirection W b) a p by
      rw [show mapDirection (mapDirection W b) a p=
        (fderiv ℝ (fderiv ℝ W) p) a b from
        congrArg (fun L : E →L[ℝ] V => L a) (mapDirection_hasFDerivAt W hW b).fderiv],
    show (fderiv ℝ (fderiv ℝ Z) p) a b=mapDirection (mapDirection Z b) a p by
      rw [show mapDirection (mapDirection Z b) a p=
        (fderiv ℝ (fderiv ℝ Z) p) a b from
        congrArg (fun L : E →L[ℝ] V => L a) (mapDirection_hasFDerivAt Z hZ b).fderiv]] at he
  simpa only [mapDirection,Function.comp_def,map_add,ContinuousLinearMap.add_apply,
    add_assoc,add_comm,add_left_comm] using he

theorem mapCovariantD_commutator (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z W : E → V)
    {p : E} (hΓ : DifferentiableAt ℝ Γ (Z p)) (hZ : ContDiffAt ℝ 2 Z p)
    (hW : ContDiffAt ℝ 2 W p) (a b : E) :
    mapCovariantD Γ Z a (mapCovariantD Γ Z b W) p-
      mapCovariantD Γ Z b (mapCovariantD Γ Z a W) p=
      connectionCurvature Γ (Z p) (mapDirection Z a p) (mapDirection Z b p) (W p) := by
  simp only [mapCovariantD,mapCovariantD_direction Γ Z W hΓ hZ hW,map_add,
    ContinuousLinearMap.add_apply,connectionCurvature]
  rw [mapDirection_commute W hW a b,mapDirection_commute Z hZ a b]
  abel

theorem mapCovariantD_torsionFree (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z : E → V)
    {p : E} (hZ : ContDiffAt ℝ 2 Z p) (hΓ : ∀ u v, Γ (Z p) u v=Γ (Z p) v u) (a b : E) :
    mapCovariantD Γ Z a (mapDirection Z b) p=mapCovariantD Γ Z b (mapDirection Z a) p := by
  simp only [mapCovariantD]
  rw [mapDirection_commute Z hZ a b,hΓ]

end Yau.LeafProofs.L23Aux
