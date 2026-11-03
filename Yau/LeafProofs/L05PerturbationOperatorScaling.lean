import Yau.LeafProofs.L05ViscosityPrimitives

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbOperatorScale {n : ℕ} (F : Sym n → ℝ) (A : Sym n) (a : ℝ) (H : Sym n) : ℝ :=
  (F (A+a • H)-F A)/a

theorem perturb_operatorScale_zero {n : ℕ} (F : Sym n → ℝ) (A : Sym n) (a : ℝ) :
    perturbOperatorScale F A a 0=0 := by simp [perturbOperatorScale]

theorem perturb_operatorScale_continuous {n : ℕ} {F : Sym n → ℝ} (hF : Continuous F)
    (A : Sym n) (a : ℝ) : Continuous (perturbOperatorScale F A a) := by
  unfold perturbOperatorScale
  have hScale : Continuous (fun H : Sym n => a • H) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun H : Sym n => a • (H : Mat n))
    exact (continuous_const : Continuous (fun _ : Sym n => a)).smul
      (continuous_subtype_val : Continuous (fun H : Sym n => (H : Mat n)))
  have hInner : Continuous (fun H : Sym n => A+a • H) := continuous_const.add hScale
  exact ((hF.comp hInner).sub continuous_const).div_const a

theorem perturb_operatorScale_elliptic {n : ℕ} {F : Sym n → ℝ} {ell L a : ℝ}
    (hF : globalElliptic F ell L) (ha : 0 < a) (A : Sym n) :
    globalElliptic (perturbOperatorScale F A a) ell L := by
  intro N P hP
  have hPos : ((a • P : Sym n) : Mat n).PosSemidef := hP.smul ha.le
  have hRaw := hF (A+a • N) (a • P) hPos
  simp only [selfAdjoint.val_smul,Matrix.trace_smul,smul_eq_mul] at hRaw
  have hId : perturbOperatorScale F A a (N+P)-perturbOperatorScale F A a N=
      (F ((A+a • N)+a • P)-F (A+a • N))/a := by
    simp only [perturbOperatorScale,smul_add,add_assoc]
    ring
  rw [hId]
  constructor
  · apply (le_div_iff₀ ha).mpr
    convert hRaw.1 using 1 <;> ring
  · apply (div_le_iff₀ ha).mpr
    convert hRaw.2 using 1 <;> ring

theorem perturb_operatorScale_concave {n : ℕ} {F : Sym n → ℝ}
    (hF : ConcaveOn ℝ univ F) {a : ℝ} (ha : 0 < a) (A : Sym n) :
    ConcaveOn ℝ univ (perturbOperatorScale F A a) := by
  refine ⟨convex_univ,?_⟩
  intro H _ K _ s t hs ht hst
  have hRaw := hF.2 (mem_univ (A+a • H)) (mem_univ (A+a • K)) hs ht hst
  have hAffine : s • (A+a • H)+t • (A+a • K)=A+a • (s • H+t • K) := by
    calc
      _ = (s+t) • A+a • (s • H+t • K) := by module
      _ = _ := by rw [hst,one_smul]
  rw [hAffine] at hRaw
  change s*perturbOperatorScale F A a H+t*perturbOperatorScale F A a K ≤
    perturbOperatorScale F A a (s • H+t • K)
  apply (le_div_iff₀ ha).mpr
  dsimp only [perturbOperatorScale]
  have hDen : (s*((F (A+a • H)-F A)/a)+t*((F (A+a • K)-F A)/a))*a=
      s*F (A+a • H)+t*F (A+a • K)-(s+t)*F A := by field_simp; ring
  rw [hDen,hst,one_mul]
  change s*F (A+a • H)+t*F (A+a • K)-F A ≤ F (A+a • (s • H+t • K))-F A
  exact sub_le_sub_right hRaw _

end Yau.LeafProofs.L05Aux
