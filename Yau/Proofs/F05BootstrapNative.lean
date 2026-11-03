import Yau.Proofs.F05BootstrapRegions
import Yau.LeafProofs.L16InteriorDataLow

/-! Native parabolic C2 fields identify the computed relative derivatives
by unique differentiation. Only each spatial slice is differentiated twice. -/

open Set
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05RelD_eq_spatialD {X : Set (Space n)} {v : Point n → ℝ} {z : Point n}
    (hX : UniqueDiffWithinAt ℝ X z.1)
    (hv : DifferentiableAt ℝ (fun x => v (x,z.2)) z.1) :
    F05RelD X v z = spatialD v z := hv.fderivWithin hX

theorem F05RelDD_eq_spatialDD {X : Set (Space n)} {v : Point n → ℝ} {z : Point n}
    (hX : UniqueDiffOn ℝ X) (hz : z.1 ∈ X)
    (hv : ∀ x ∈ X, ContDiffAt ℝ 2 (fun y => v (y,z.2)) x) :
    F05RelDD X v z = spatialDD v z := by
  have hFirst : EqOn (fun x => F05RelD X v (x,z.2))
      (fun x => fderiv ℝ (fun y => v (y,z.2)) x) X := by
    intro x hx
    exact (hv x hx).differentiableAt (by norm_num) |>.fderivWithin (hX x hx)
  rw [F05RelDD,fderivWithin_congr hFirst (hFirst hz)]
  exact (((hv z.1 hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).fderivWithin (hX z.1 hz)

theorem F05RelT_eq_timeD {X : Set (Space n)} {l r : ℝ} (v : Point n → ℝ)
    {z : Point n} (hz : z.1 ∈ X) :
    F05RelT (Icc l r) v z = timeD (cylinder X l r) v z := by
  have hFiber : {t | (z.1,t) ∈ cylinder X l r} = Icc l r := by
    ext t
    simp only [cylinder,mem_prod,hz,true_and,mem_ofPred_eq]
  simp only [F05RelT,timeD,hFiber]

theorem F05_native_c2_to_relative {X : Set (Space n)} {l r : ℝ} {v : Point n → ℝ}
    (hX : UniqueDiffOn ℝ X) (hv : C2 (cylinder X l r) v) :
    F05RelC2 X (Icc l r) v := by
  have hD (z : Point n) (hz : z ∈ cylinder X l r) : F05RelD X v z = spatialD v z :=
    F05RelD_eq_spatialD (hX z.1 hz.1) ((hv.2.2.2.2.1 z hz).differentiableAt (by norm_num))
  have hDD (z : Point n) (hz : z ∈ cylinder X l r) : F05RelDD X v z = spatialDD v z :=
    F05RelDD_eq_spatialDD hX hz.1 (fun x hx => hv.2.2.2.2.1 (x,z.2) ⟨hx,hz.2⟩)
  refine ⟨hv.1,hv.2.1.congr hD,hv.2.2.1.congr hDD,
    hv.2.2.2.1.congr (fun z hz => F05RelT_eq_timeD v hz.1),?_,?_⟩
  · intro t ht x hx
    exact (hv.2.2.2.2.1 (x,t) ⟨hx,ht⟩).contDiffWithinAt
  · intro z hz
    have hFiber : {t | (z.1,t) ∈ cylinder X l r} = Icc l r := by
      ext t
      simp only [cylinder,mem_prod,hz.1,true_and,mem_ofPred_eq]
    simpa only [hFiber] using hv.2.2.2.2.2 z hz

theorem F05RelOp_eq_linearOp {X : Set (Space n)} {l r : ℝ} {v : Point n → ℝ}
    (hX : UniqueDiffOn ℝ X) (hv : C2 (cylinder X l r) v)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) {z : Point n}
    (hz : z ∈ cylinder X l r) :
    F05RelOp X (Icc l r) a b v z = linearOp (cylinder X l r) a b v z := by
  rw [F05RelOp,F05RelT_eq_timeD v hz.1,
    F05RelDD_eq_spatialDD hX hz.1 (fun x hx => hv.2.2.2.2.1 (x,z.2) ⟨hx,hz.2⟩),
    F05RelD_eq_spatialD (hX z.1 hz.1) ((hv.2.2.2.2.1 z hz).differentiableAt (by norm_num))]
  rfl

end Yau.Proofs.F05Aux
