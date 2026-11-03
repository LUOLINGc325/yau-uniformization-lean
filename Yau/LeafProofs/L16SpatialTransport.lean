import Yau.LeafProofs.L16LinearizedSource

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def spatialTranslatePoint {n : ℕ} (v : Space n) (p : Point n) : Point n := (p.1+v,p.2)

def spatialTranslate {n : ℕ} {V : Type*} (v : Space n) (u : Point n → V) : Point n → V :=
  fun p => u (spatialTranslatePoint v p)

theorem spatialD_spatialTranslate {n : ℕ} (v : Space n) (u : Point n → ℝ) (p : Point n) :
    spatialD (spatialTranslate v u) p = spatialD u (spatialTranslatePoint v p) := by
  exact fderiv_comp_add_right (𝕜 := ℝ) (f := fun x => u (x,p.2)) (x := p.1) v

theorem spatialDD_spatialTranslate {n : ℕ} (v : Space n) (u : Point n → ℝ) (p : Point n) :
    spatialDD (spatialTranslate v u) p = spatialDD u (spatialTranslatePoint v p) := by
  change fderiv ℝ (fderiv ℝ (fun x => u (x+v,p.2))) p.1 =
    fderiv ℝ (fderiv ℝ (fun x => u (x,p.2))) (p.1+v)
  rw [show fderiv ℝ (fun x => u (x+v,p.2)) =
    (fun x => fderiv ℝ (fun y => u (y,p.2)) (x+v)) from funext (fun x =>
      fderiv_comp_add_right (𝕜 := ℝ) (f := fun y => u (y,p.2)) (x := x) v)]
  exact fderiv_comp_add_right (𝕜 := ℝ) (f := fderiv ℝ (fun y => u (y,p.2))) (x := p.1) v

theorem timeD_spatialTranslate {n : ℕ} (v : Space n) (u : Point n → ℝ) (T : ℝ) (p : Point n) :
    timeD (cylinder Set.univ 0 T) (spatialTranslate v u) p =
      timeD (cylinder Set.univ 0 T) u (spatialTranslatePoint v p) := by
  simp only [timeD,spatialTranslate,spatialTranslatePoint,Yau.Parabolic.cylinder,
    Set.mem_prod,Set.mem_univ,true_and]

theorem c2_spatialTranslate {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (v : Space n) :
    C2 (cylinder Set.univ 0 T) (spatialTranslate v u) := by
  let Q : Set (Point n) := cylinder Set.univ 0 T
  have hMap : Set.MapsTo (spatialTranslatePoint v) Q Q := fun p hp => ⟨Set.mem_univ _,hp.2⟩
  have hCont : ContinuousOn (spatialTranslatePoint v) Q :=
    ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn
  refine ⟨hu.1.comp hCont hMap,?_,?_,?_,?_,?_⟩
  · exact (hu.2.1.comp hCont hMap).congr (fun p _ => spatialD_spatialTranslate v u p)
  · exact (hu.2.2.1.comp hCont hMap).congr (fun p _ => spatialDD_spatialTranslate v u p)
  · exact (hu.2.2.2.1.comp hCont hMap).congr (fun p _ => timeD_spatialTranslate v u T p)
  · intro p hp
    have h := (hu.2.2.2.2.1 _ (hMap hp)).comp p.1
      (show ContDiffAt ℝ 2 (fun x : Space n => x+v) p.1 from contDiffAt_id.add contDiffAt_const)
    exact h
  · intro p hp
    simpa only [spatialTranslate,spatialTranslatePoint,Yau.Parabolic.cylinder,
      Set.mem_prod,Set.mem_univ,true_and] using hu.2.2.2.2.2 _ (hMap hp)

theorem c2_spatialDifferenceQuotient {n : ℕ} {T : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (e : Space n) (h : ℝ) :
    C2 (cylinder Set.univ 0 T) (spatialDifferenceQuotient u e h) := by
  exact c2_const_smul (c2_sub (c2_spatialTranslate hu (h • e)) hu) h⁻¹

theorem linearOp_spatialTranslate {n : ℕ} (v : Space n) (u : Point n → ℝ) (T : ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (p : Point n) :
    linearOp (cylinder Set.univ 0 T) (spatialTranslate v a) (spatialTranslate v b)
      (spatialTranslate v u) p = spatialTranslate v (linearOp (cylinder Set.univ 0 T) a b u) p := by
  simp only [linearOp,spatialD_spatialTranslate,spatialDD_spatialTranslate,timeD_spatialTranslate]
  rfl

theorem linearOp_spatialTranslate_commutator {n : ℕ} (v : Space n) (u : Point n → ℝ) (T : ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (p : Point n) :
    linearOp (cylinder Set.univ 0 T) a b (spatialTranslate v u) p =
      spatialTranslate v (linearOp (cylinder Set.univ 0 T) a b u) p+
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        (spatialTranslate v a p i j-a p i j)*spatialDD u (spatialTranslatePoint v p) (Yau.realVec i) (Yau.realVec j))+
      ∑ i : Yau.RIdx n,
        (spatialTranslate v b p i-b p i)*spatialD u (spatialTranslatePoint v p) (Yau.realVec i) := by
  simp only [spatialTranslate,linearOp,spatialD_spatialTranslate,spatialDD_spatialTranslate,timeD_spatialTranslate,
    sub_mul,Finset.sum_sub_distrib]
  ring

theorem linearOp_spatialDifferenceQuotient {n : ℕ} {T : ℝ} {u f : Point n → ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u)
    (hOp : ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p)
    (e : Space n) (h : ℝ) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T) a b (spatialDifferenceQuotient u e h) p =
      quotientSpatialSource e h u a b f p := by
  have hq : spatialTranslatePoint (h • e) p ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2⟩
  have hQ : spatialDifferenceQuotient u e h = h⁻¹ • (fun q => spatialTranslate (h • e) u q-u q) := rfl
  rw [hQ,linearOp_const_smul (c2_sub (c2_spatialTranslate hu (h • e)) hu) h⁻¹ hp,
    linearOp_sub (c2_spatialTranslate hu (h • e)) hu hp,linearOp_spatialTranslate_commutator]
  change h⁻¹*(linearOp (cylinder Set.univ 0 T) a b u (spatialTranslatePoint (h • e) p)+_+_-_) = _
  rw [hOp _ hq,hOp p hp]
  let q := spatialTranslatePoint (h • e) p
  let H := spatialDD u q
  let G := spatialD u q
  have hA : (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      spatialDifferenceQuotient a e h p i j*H (Yau.realVec i) (Yau.realVec j)) =
      h⁻¹*(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        (a q i j-a p i j)*H (Yau.realVec i) (Yau.realVec j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [spatialDifferenceQuotient,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,q,spatialTranslatePoint]
    ring
  have hB : (∑ i : Yau.RIdx n,
      spatialDifferenceQuotient (fun q => b q i) e h p*G (Yau.realVec i)) =
      h⁻¹*(∑ i : Yau.RIdx n, (b q i-b p i)*G (Yau.realVec i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [spatialDifferenceQuotient,smul_eq_mul,q,spatialTranslatePoint]
    ring
  change h⁻¹*(f q+_+_-f p) =
    spatialDifferenceQuotient f e h p+
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        spatialDifferenceQuotient a e h p i j*H (Yau.realVec i) (Yau.realVec j))+
      ∑ i : Yau.RIdx n, spatialDifferenceQuotient (fun q => b q i) e h p*G (Yau.realVec i)
  rw [hA,hB]
  dsimp only [spatialDifferenceQuotient,spatialTranslate,q,H,G,spatialTranslatePoint]
  simp only [smul_eq_mul]
  ring

end Yau.LeafProofs.L16Aux
