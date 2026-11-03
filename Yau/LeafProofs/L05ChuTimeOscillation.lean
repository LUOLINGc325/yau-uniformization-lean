import Yau.LeafProofs.L05ChuDiniAbsorption
import Yau.LeafProofs.L05MongeTimeTransport

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic L16Aux

theorem chu_parabolicDistance_timeTranslate {n : ℕ} (l : ℝ) (p q : Point n) :
    parabolicDistance (timeTranslatePoint l p) (timeTranslatePoint l q)=parabolicDistance p q := by
  simp only [parabolicDistance,timeTranslatePoint,add_sub_add_right_eq_sub]

theorem chuOscillation_timeTranslate {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (l T : ℝ) (J : Point n → V) :
    chuOscillation (cylinder Set.univ 0 T) (timeTranslate l J)=
      chuOscillation (cylinder Set.univ l (T+l)) J := by
  funext radius
  unfold chuOscillation
  congr 1
  ext v
  constructor
  · rintro (rfl | ⟨p,hp,q,hq,hpq,hv⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨timeTranslatePoint l p,⟨Set.mem_univ _,?_,?_⟩,
        timeTranslatePoint l q,⟨Set.mem_univ _,?_,?_⟩,?_,hv⟩
      · change l ≤ p.2+l
        linarith only [hp.2.1]
      · change p.2+l ≤ T+l
        linarith only [hp.2.2]
      · change l ≤ q.2+l
        linarith only [hq.2.1]
      · change q.2+l ≤ T+l
        linarith only [hq.2.2]
      · rw [chu_parabolicDistance_timeTranslate]
        exact hpq
  · rintro (rfl | ⟨p,hp,q,hq,hpq,hv⟩)
    · exact Or.inl rfl
    · let p' : Point n := (p.1,p.2-l)
      let q' : Point n := (q.1,q.2-l)
      have hpc : timeTranslatePoint l p'=p := by ext <;> simp only [timeTranslatePoint,p',sub_add_cancel]
      have hqc : timeTranslatePoint l q'=q := by ext <;> simp only [timeTranslatePoint,q',sub_add_cancel]
      refine Or.inr ⟨p',⟨Set.mem_univ _,sub_nonneg.mpr hp.2.1,?_⟩,
        q',⟨Set.mem_univ _,sub_nonneg.mpr hq.2.1,?_⟩,?_,?_⟩
      · dsimp only [p']
        linarith only [hp.2.2]
      · dsimp only [q']
        linarith only [hq.2.2]
      · rw [← chu_parabolicDistance_timeTranslate l p' q',hpc,hqc]
        exact hpq
      · simpa only [timeTranslate,hpc,hqc] using hv

theorem chu_c2_timeTranslate_slab_zero {n : ℕ} {l r : ℝ} (hlr : l < r)
    {w : Point n → ℝ} (hw : C2 (cylinder Set.univ l r) w) :
    C2 (cylinder Set.univ 0 (r-l)) (timeTranslate l w) := by
  have hws : C2 (cylinder Set.univ ((0:ℝ)+l) ((r-l)+l)) w := by
    simpa only [zero_add,sub_add_cancel] using hw
  exact c2_timeTranslate_on_space (sub_pos.mpr hlr) hws

theorem chu_constant_linearOp_timeTranslate_zero {n : ℕ} {l r : ℝ} (hlr : l < r)
    (A : Mat n) {w : Point n → ℝ} (hw : C2 (cylinder Set.univ l r) w)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 (r-l)) :
    linearOp (cylinder Set.univ 0 (r-l)) (fun _ => A) (fun _ _ => 0) (timeTranslate l w) p=
      linearOp (cylinder Set.univ l r) (fun _ => A) (fun _ _ => 0) w (timeTranslatePoint l p) := by
  have hws : C2 (cylinder Set.univ ((0:ℝ)+l) ((r-l)+l)) w := by
    simpa only [zero_add,sub_add_cancel] using hw
  have hh := linearOp_timeTranslate_on_space (sub_pos.mpr hlr) hws (fun _ => A) (fun _ _ => 0) hp
  simp only [zero_add,sub_add_cancel] at hh
  convert! hh using 1

end Yau.LeafProofs.L05Aux
