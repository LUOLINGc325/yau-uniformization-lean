import Yau.LeafProofs.L16WordSource
import Yau.LeafProofs.L16JointDerivative

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Each contraction in a word source has the joint regularity of the word
fields: its spatial derivatives are themselves longer words on the slab. -/
theorem wordCorrection_contDiffOn_of_words {n : ℕ} {T : ℝ} {r : ℕ∞ω}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hC2 : ∀ w : List (Space n), C2 (cylinder Set.univ 0 T) (spatialWordDerivative w u))
    (hU : ∀ w : List (Space n), ContDiffOn ℝ r (spatialWordDerivative w u) (cylinder Set.univ 0 T))
    (hA : ∀ s : List (Space n), ContDiffOn ℝ r (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hB : ∀ (s : List (Space n)) i,
      ContDiffOn ℝ r (spatialWordDerivative s (fun p => b p i)) (cylinder Set.univ 0 T))
    (s t : List (Space n)) :
    ContDiffOn ℝ r (wordCorrection a b u s t) (cylinder Set.univ 0 T) := by
  have hDD (i j : Yau.RIdx n) : ContDiffOn ℝ r
      (fun p => spatialDD (spatialWordDerivative t u) p (Yau.realVec i) (Yau.realVec j))
      (cylinder Set.univ 0 T) := by
    apply (hU (Yau.realVec i :: Yau.realVec j :: t)).congr
    intro p hp
    exact (spatialPartial_spatialPartial_eq_spatialDD (hC2 t) _ _ hp).symm
  have hD (i : Yau.RIdx n) : ContDiffOn ℝ r
      (fun p => spatialD (spatialWordDerivative t u) p (Yau.realVec i))
      (cylinder Set.univ 0 T) := hU (Yau.realVec i :: t)
  have hEntry (i j : Yau.RIdx n) : ContDiffOn ℝ r
      (fun p => spatialWordDerivative s a p i j) (cylinder Set.univ 0 T) :=
    (matrixEntryCLM i j).contDiff.comp_contDiffOn (hA s)
  exact (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (hEntry i j).mul (hDD i j)))).add
      (ContDiffOn.sum (fun i _ => (hB s i).mul (hD i)))

theorem contDiffOn_list_sum {n : ℕ} {r : ℕ∞ω} {Q : Set (Point n)} {ι : Type*}
    (xs : List ι) (f : ι → Point n → ℝ)
    (hf : ∀ i ∈ xs, ContDiffOn ℝ r (f i) Q) :
    ContDiffOn ℝ r (fun p => (xs.map (fun i => f i p)).sum) Q := by
  induction xs with
  | nil => exact contDiffOn_const
  | cons i xs ih =>
    exact (hf i List.mem_cons_self).add (ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)))

theorem wordSource_contDiffOn_of_words {n : ℕ} {T : ℝ} {r : ℕ∞ω}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hC2 : ∀ w : List (Space n), C2 (cylinder Set.univ 0 T) (spatialWordDerivative w u))
    (hU : ∀ w : List (Space n), ContDiffOn ℝ r (spatialWordDerivative w u) (cylinder Set.univ 0 T))
    (hA : ∀ s : List (Space n), ContDiffOn ℝ r (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hB : ∀ (s : List (Space n)) i,
      ContDiffOn ℝ r (spatialWordDerivative s (fun p => b p i)) (cylinder Set.univ 0 T))
    (hF : ∀ s : List (Space n), ContDiffOn ℝ r (spatialWordDerivative s f) (cylinder Set.univ 0 T))
    (w : List (Space n)) :
    ContDiffOn ℝ r (wordSource a b f u w) (cylinder Set.univ 0 T) := by
  exact (hF w).add (contDiffOn_list_sum (commutatorSplits w)
    (fun st => wordCorrection a b u st.1 st.2)
    (fun st _ => wordCorrection_contDiffOn_of_words hC2 hU hA hB st.1 st.2))

/-- The actual PDE determines the one-sided temporal derivative on the closed
slab in terms of the word source and the original operator coefficients. -/
theorem word_timeD_eq_source_correction {n : ℕ} {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    {w : List (Space n)} {p : Point n}
    (hPDE : linearOp (cylinder Set.univ 0 T) a b (spatialWordDerivative w u) p =
      wordSource a b f u w p) :
    timeD (cylinder Set.univ 0 T) (spatialWordDerivative w u) p =
      wordSource a b f u w p + wordCorrection a b u [] w p := by
  simp only [linearOp,wordCorrection,spatialWordDerivative] at hPDE ⊢
  linarith

/-- All spatial word fields are jointly smooth on the closed slab once they
have parabolic C² regularity and satisfy their actual differentiated PDEs.
Only the original coefficient and forcing words are assumed smooth. -/
theorem spatialWords_contDiffOn_infty_of_c2_pde {n : ℕ} {T : ℝ} (hT : 0 < T)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hC2 : ∀ w : List (Space n), C2 (cylinder Set.univ 0 T) (spatialWordDerivative w u))
    (hPDE : ∀ (w : List (Space n)) p, p ∈ cylinder Set.univ 0 T →
      linearOp (cylinder Set.univ 0 T) a b (spatialWordDerivative w u) p = wordSource a b f u w p)
    (hA : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hB : ∀ (s : List (Space n)) i,
      ContDiffOn ℝ ∞ (spatialWordDerivative s (fun p => b p i)) (cylinder Set.univ 0 T))
    (hF : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s f) (cylinder Set.univ 0 T)) :
    ∀ w : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative w u) (cylinder Set.univ 0 T) := by
  have hFinite : ∀ m : ℕ, ∀ w : List (Space n),
      ContDiffOn ℝ (m : ℕ∞ω) (spatialWordDerivative w u) (cylinder Set.univ 0 T) := by
    intro m
    induction m with
    | zero =>
      intro w
      exact contDiffOn_zero.mpr (hC2 w).1
    | succ m ih =>
      have hAm (s : List (Space n)) := (contDiffOn_infty.mp (hA s)) m
      have hBm (s : List (Space n)) (i : Yau.RIdx n) := (contDiffOn_infty.mp (hB s i)) m
      have hFm (s : List (Space n)) := (contDiffOn_infty.mp (hF s)) m
      have hH (w : List (Space n)) : ContDiffOn ℝ (m : ℕ∞ω)
          (fun p => wordSource a b f u w p + wordCorrection a b u [] w p)
          (cylinder Set.univ 0 T) :=
        (wordSource_contDiffOn_of_words hC2 ih hAm hBm hFm w).add
          (wordCorrection_contDiffOn_of_words hC2 ih hAm hBm [] w)
      intro w
      rw [Nat.cast_add,Nat.cast_one]
      apply contDiffOn_succ_of_fderiv_apply
        (fun p hp => (c2_hasFDerivWithinAt (hC2 w) hp).differentiableWithinAt)
        (by simp)
      intro z
      apply ((ih (z.1 :: w)).add (contDiffOn_const.mul (hH w))).congr
      intro p hp
      rw [c2_fderivWithin hT (hC2 w) hp]
      simp only [parabolicFirstDeriv,add_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd',smul_eq_mul]
      rw [word_timeD_eq_source_correction (hPDE w p hp)]
      rfl
  intro w
  exact contDiffOn_infty.mpr (fun m => hFinite m w)

theorem contDiffOn_infty_of_spatialWords_c2_pde {n : ℕ} {T : ℝ} (hT : 0 < T)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hC2 : ∀ w : List (Space n), C2 (cylinder Set.univ 0 T) (spatialWordDerivative w u))
    (hPDE : ∀ (w : List (Space n)) p, p ∈ cylinder Set.univ 0 T →
      linearOp (cylinder Set.univ 0 T) a b (spatialWordDerivative w u) p = wordSource a b f u w p)
    (hA : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hB : ∀ (s : List (Space n)) i,
      ContDiffOn ℝ ∞ (spatialWordDerivative s (fun p => b p i)) (cylinder Set.univ 0 T))
    (hF : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s f) (cylinder Set.univ 0 T)) :
    ContDiffOn ℝ ∞ u (cylinder Set.univ 0 T) :=
  spatialWords_contDiffOn_infty_of_c2_pde hT hC2 hPDE hA hB hF []

end Yau.LeafProofs.L16Aux
