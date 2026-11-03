import Yau.LeafProofs.L16TimeTransport
import Yau.LeafProofs.L16ClassicalCutoff

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem timeTranslatePoint_mem_cylinder_on_space {n : ℕ} {O : Set (Space n)} {l r τ : ℝ} {p : Point n}
    (hp : p ∈ cylinder O l r) :
    timeTranslatePoint τ p ∈ cylinder O (l+τ) (r+τ) :=
  ⟨hp.1,add_le_add hp.2.1 le_rfl,add_le_add hp.2.2 le_rfl⟩

theorem holderBound_timeTranslate_on_space {n : ℕ} {O : Set (Space n)} {V : Type*} [NormedAddCommGroup V]
    {α C l r τ : ℝ} {u : Point n → V}
    (hu : HolderBound α (cylinder O (l+τ) (r+τ)) u C) :
    HolderBound α (cylinder O l r) (timeTranslate τ u) C := by
  refine ⟨hu.1,fun p hp => hu.2.1 _ (timeTranslatePoint_mem_cylinder_on_space hp),?_⟩
  intro p hp q hq
  have h := hu.2.2 _ (timeTranslatePoint_mem_cylinder_on_space hp) _ (timeTranslatePoint_mem_cylinder_on_space hq)
  simpa only [timeTranslate,timeTranslatePoint,holderWeight,Prod.fst,Prod.snd,add_sub_add_right_eq_sub] using h

theorem hasDerivWithinAt_timeTranslate_on_space {n : ℕ} {O : Set (Space n)} {l r τ : ℝ} {u : Point n → ℝ}
    {p : Point n} (_hp : p ∈ cylinder O l r)
    (hu : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ)) :
    HasDerivWithinAt (fun t => timeTranslate τ u (p.1,t))
      (derivWithin (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ))
      (Set.Icc l r) p.2 := by
  have h := hu.hasDerivWithinAt.comp p.2 ((hasDerivAt_id p.2).add_const τ).hasDerivWithinAt
    (show Set.MapsTo (fun t : ℝ => t+τ) (Set.Icc l r) (Set.Icc (l+τ) (r+τ)) from
      fun t ht => ⟨add_le_add ht.1 le_rfl,add_le_add ht.2 le_rfl⟩)
  convert! h using 1
  simp only [mul_one]

theorem timeD_timeTranslate_on_space {n : ℕ} {O : Set (Space n)} {l r τ : ℝ} (hlr : l < r) {u : Point n → ℝ}
    {p : Point n} (hp : p ∈ cylinder O l r)
    (hu : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ)) :
    timeD (cylinder O l r) (timeTranslate τ u) p =
      timeD (cylinder O (l+τ) (r+τ)) u (timeTranslatePoint τ p) := by
  have h := (hasDerivWithinAt_timeTranslate_on_space hp hu).derivWithin (uniqueDiffOn_Icc hlr _ hp.2)
  simpa only [timeD,timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    hp.1,true_and,Set.ofPred_mem_eq] using h

theorem c2_timeTranslate_on_space {n : ℕ} {O : Set (Space n)} {l r τ : ℝ} (hlr : l < r) {u : Point n → ℝ}
    (hu : C2 (cylinder O (l+τ) (r+τ)) u) :
    C2 (cylinder O l r) (timeTranslate τ u) := by
  let Q : Set (Point n) := cylinder O l r
  let Q' : Set (Point n) := cylinder O (l+τ) (r+τ)
  have hMap : Set.MapsTo (timeTranslatePoint τ) Q Q' := fun _ hp => timeTranslatePoint_mem_cylinder_on_space hp
  have hCont : ContinuousOn (timeTranslatePoint (n := n) τ) Q :=
    (timeTranslatePoint_contDiff τ).continuous.continuousOn
  have hU (p : Point n) (hp : p ∈ Q) :
      DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ) := by
    simpa only [timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,hp.1,true_and,Set.ofPred_mem_eq]
      using hu.2.2.2.2.2 _ (hMap hp)
  refine ⟨hu.1.comp hCont hMap,hu.2.1.comp hCont hMap,
    hu.2.2.1.comp hCont hMap,?_,?_,?_⟩
  · apply (hu.2.2.2.1.comp hCont hMap).congr
    intro p hp
    exact timeD_timeTranslate_on_space hlr hp (hU p hp)
  · intro p hp
    exact hu.2.2.2.2.1 _ (hMap hp)
  · intro p hp
    simpa only [Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,hp.1,true_and,Set.ofPred_mem_eq]
      using (hasDerivWithinAt_timeTranslate_on_space hp (hU p hp)).differentiableWithinAt

theorem linearOp_timeTranslate_on_space {n : ℕ} {O : Set (Space n)} {l r τ : ℝ} (hlr : l < r)
    {u : Point n → ℝ} (hu : C2 (cylinder O (l+τ) (r+τ)) u)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {p : Point n} (hp : p ∈ cylinder O l r) :
    linearOp (cylinder O l r) (timeTranslate τ a) (timeTranslate τ b)
      (timeTranslate τ u) p =
      linearOp (cylinder O (l+τ) (r+τ)) a b u (timeTranslatePoint τ p) := by
  have hU : DifferentiableWithinAt ℝ (fun t => u (p.1,t))
      (Set.Icc (l+τ) (r+τ)) (p.2+τ) := by
    simpa only [timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,hp.1,true_and,Set.ofPred_mem_eq]
      using hu.2.2.2.2.2 _ (timeTranslatePoint_mem_cylinder_on_space hp)
  simp only [linearOp,timeD_timeTranslate_on_space hlr hp hU,spatialD_timeTranslate,spatialDD_timeTranslate]
  rfl

theorem schauderBound_timeTranslate_on_space {n : ℕ} {O : Set (Space n)} {α C l r τ : ℝ} (hlr : l < r)
    {u : Point n → ℝ} (hu : SchauderBound α (cylinder O (l+τ) (r+τ)) u C) :
    SchauderBound α (cylinder O l r) (timeTranslate τ u) C := by
  refine ⟨c2_timeTranslate_on_space hlr hu.1,hu.2.1,
    fun p hp => hu.2.2.1 _ (timeTranslatePoint_mem_cylinder_on_space hp),
    holderBound_timeTranslate_on_space hu.2.2.2.1,?_⟩
  apply holderBound_congr_on (holderBound_timeTranslate_on_space hu.2.2.2.2)
  intro p hp
  apply (timeD_timeTranslate_on_space hlr hp _).symm
  simpa only [timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    hp.1,true_and,Set.ofPred_mem_eq] using hu.1.2.2.2.2.2 _ (timeTranslatePoint_mem_cylinder_on_space hp)

end Yau.LeafProofs.L16Aux
