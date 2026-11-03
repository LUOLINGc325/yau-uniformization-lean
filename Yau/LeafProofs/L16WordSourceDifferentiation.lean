import Yau.LeafProofs.L16WordSource

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem wordCorrection_spatial_calc {n : ℕ} {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (s t : List (Space n))
    (ha : ContDiffOn ℝ ∞ (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hb : ∀ i, ContDiffOn ℝ ∞ (spatialWordDerivative s (fun q => b q i)) (cylinder Set.univ 0 T))
    (hu : C2 (cylinder Set.univ 0 T) (spatialWordDerivative t u))
    (hSlices : ∀ τ ∈ Set.Icc 0 T, ContDiff ℝ 3 (fun x : Space n => spatialWordDerivative t u (x,τ)))
    (e : Space n) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    DifferentiableAt ℝ (fun x => wordCorrection a b u s t (x,p.2)) p.1 ∧
      spatialPartial (wordCorrection a b u s t) e p =
        wordCorrection a b u (e::s) t p+wordCorrection a b u s (e::t) p := by
  let A := spatialWordDerivative s a
  let B : Yau.RIdx n → Point n → ℝ := fun i => spatialWordDerivative s (fun q => b q i)
  let V := spatialWordDerivative t u
  let P : Yau.RIdx n → Yau.RIdx n → Point n → ℝ := fun i j q =>
    A q i j*spatialDD V q (Yau.realVec i) (Yau.realVec j)
  let R : Yau.RIdx n → Point n → ℝ := fun i q => B i q*spatialD V q (Yau.realVec i)
  have hA : DifferentiableAt ℝ (fun x => A (x,p.2)) p.1 :=
    (cylinder_spatialSlice_contDiff ha hp.2).differentiable (by simp) p.1
  have hB (i : Yau.RIdx n) : DifferentiableAt ℝ (fun x => B i (x,p.2)) p.1 :=
    (cylinder_spatialSlice_contDiff (hb i) hp.2).differentiable (by simp) p.1
  have hAE (i j : Yau.RIdx n) := matrixEntry_spatial_differentiableAt hA i j
  have hH (i j : Yau.RIdx n) := spatial_hessian_component_differentiableAt hSlices (Yau.realVec i) (Yau.realVec j) hp
  have hG (i : Yau.RIdx n) := spatial_gradient_component_differentiableAt hu (Yau.realVec i) hp
  have hP (i j : Yau.RIdx n) : DifferentiableAt ℝ (fun x => P i j (x,p.2)) p.1 := (hAE i j).mul (hH i j)
  have hR (i : Yau.RIdx n) : DifferentiableAt ℝ (fun x => R i (x,p.2)) p.1 := (hB i).mul (hG i)
  have hRow (i : Yau.RIdx n) : DifferentiableAt ℝ (fun x => ∑ j : Yau.RIdx n, P i j (x,p.2)) p.1 :=
    DifferentiableAt.fun_sum (fun j _ => hP i j)
  have hPA : DifferentiableAt ℝ (fun x => ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, P i j (x,p.2)) p.1 :=
    DifferentiableAt.fun_sum (fun i _ => hRow i)
  have hRB : DifferentiableAt ℝ (fun x => ∑ i : Yau.RIdx n, R i (x,p.2)) p.1 :=
    DifferentiableAt.fun_sum (fun i _ => hR i)
  refine ⟨hPA.add hRB,?_⟩
  have hPEq (i j : Yau.RIdx n) : spatialPartial (P i j) e p =
      spatialWordDerivative (e::s) a p i j*spatialDD (spatialWordDerivative t u) p (Yau.realVec i) (Yau.realVec j)+
      spatialWordDerivative s a p i j*spatialDD (spatialWordDerivative (e::t) u) p (Yau.realVec i) (Yau.realVec j) := by
    change spatialPartial (fun q => A q i j*spatialDD V q (Yau.realVec i) (Yau.realVec j)) e p = _
    rw [spatialPartial_mul (hAE i j) (hH i j) e,spatialPartial_matrix_entry hA e i j,
      spatialPartial_hessian_component_eq hSlices e (Yau.realVec i) (Yau.realVec j) hp]
    rfl
  have hREq (i : Yau.RIdx n) : spatialPartial (R i) e p =
      spatialWordDerivative (e::s) (fun q => b q i) p*spatialD (spatialWordDerivative t u) p (Yau.realVec i)+
      spatialWordDerivative s (fun q => b q i) p*spatialD (spatialWordDerivative (e::t) u) p (Yau.realVec i) := by
    change spatialPartial (fun q => B i q*spatialD V q (Yau.realVec i)) e p = _
    rw [spatialPartial_mul (hB i) (hG i) e,spatialPartial_gradient_component_eq hu e (Yau.realVec i) hp]
    rfl
  have hPASum : spatialPartial (fun q => ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, P i j q) e p =
      ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
        (spatialWordDerivative (e::s) a p i j*spatialDD (spatialWordDerivative t u) p (Yau.realVec i) (Yau.realVec j)+
        spatialWordDerivative s a p i j*spatialDD (spatialWordDerivative (e::t) u) p (Yau.realVec i) (Yau.realVec j)) := by
    rw [spatialPartial_finset_sum Finset.univ (fun i _ => hRow i) e]
    apply Finset.sum_congr rfl
    intro i _
    rw [spatialPartial_finset_sum Finset.univ (fun j _ => hP i j) e]
    exact Finset.sum_congr rfl (fun j _ => hPEq i j)
  have hRBSum : spatialPartial (fun q => ∑ i : Yau.RIdx n, R i q) e p =
      ∑ i : Yau.RIdx n,
        (spatialWordDerivative (e::s) (fun q => b q i) p*spatialD (spatialWordDerivative t u) p (Yau.realVec i)+
        spatialWordDerivative s (fun q => b q i) p*spatialD (spatialWordDerivative (e::t) u) p (Yau.realVec i)) := by
    rw [spatialPartial_finset_sum Finset.univ (fun i _ => hR i) e]
    exact Finset.sum_congr rfl (fun i _ => hREq i)
  change spatialPartial (fun q => (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, P i j q)+(∑ i : Yau.RIdx n, R i q)) e p = _
  rw [spatialPartial_add hPA hRB e,hPASum,hRBSum]
  simp only [wordCorrection,Finset.sum_add_distrib]
  ring

theorem wordSource_spatial_calc {n : ℕ} {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hA : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s a) (cylinder Set.univ 0 T))
    (hB : ∀ (s : List (Space n)) i, ContDiffOn ℝ ∞ (spatialWordDerivative s (fun p => b p i)) (cylinder Set.univ 0 T))
    (hF : ∀ s : List (Space n), ContDiffOn ℝ ∞ (spatialWordDerivative s f) (cylinder Set.univ 0 T))
    (w : List (Space n))
    (hU : ∀ st ∈ commutatorSplits w, C2 (cylinder Set.univ 0 T) (spatialWordDerivative st.2 u))
    (hSlices : ∀ st ∈ commutatorSplits w, ∀ τ ∈ Set.Icc 0 T,
      ContDiff ℝ 3 (fun x : Space n => spatialWordDerivative st.2 u (x,τ)))
    (e : Space n) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    DifferentiableAt ℝ (fun x => wordSource a b f u w (x,p.2)) p.1 ∧
      spatialPartial (wordSource a b f u w) e p = wordSourceDerivative a b f u e w p := by
  have hEach (st : List (Space n) × List (Space n)) (hst : st ∈ commutatorSplits w) :=
    wordCorrection_spatial_calc st.1 st.2 (hA st.1) (hB st.1) (hU st hst) (hSlices st hst) e hp
  have hFDiff : DifferentiableAt ℝ (fun x => spatialWordDerivative w f (x,p.2)) p.1 :=
    (cylinder_spatialSlice_contDiff (hF w) hp.2).differentiable (by simp) p.1
  have hListDiff := spatial_list_sum_differentiableAt (commutatorSplits w) (fun st hst => (hEach st hst).1)
  refine ⟨hFDiff.add hListDiff,?_⟩
  change spatialPartial (fun q => spatialWordDerivative w f q+
    ((commutatorSplits w).map (fun st => wordCorrection a b u st.1 st.2 q)).sum) e p = _
  rw [spatialPartial_add hFDiff hListDiff e,
    spatialPartial_list_sum (commutatorSplits w) (fun st hst => (hEach st hst).1) e]
  change spatialWordDerivative (e::w) f p+_ = spatialWordDerivative (e::w) f p+_
  congr 1
  apply congrArg List.sum
  exact List.map_congr_left (fun st hst => (hEach st hst).2)

theorem linearizedSpatialSource_wordSource {n : ℕ}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ)
    (e : Space n) (w : List (Space n)) (p : Point n)
    (hDerivative : spatialPartial (wordSource a b f u w) e p = wordSourceDerivative a b f u e w p) :
    linearizedSpatialSource e (spatialWordDerivative w u) a b (wordSource a b f u w) p =
      wordSource a b f u (e::w) p := by
  rw [wordSource_cons]
  unfold linearizedSpatialSource
  rw [hDerivative]
  simp only [wordCorrection,spatialWordDerivative]
  ring

end Yau.LeafProofs.L16Aux
