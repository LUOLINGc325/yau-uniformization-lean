import Yau.LeafProofs.L05PucciHarnackDyadicShrinking
import Yau.LeafProofs.L05PucciHarnackCountableCover
import Yau.LeafProofs.L05PucciHarnackDecayConstants

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackGridDense {n : ℕ} (h0 q : ℝ) (A : Set (Point n)) (Q : harnackGridIndex n) : Prop :=
  q*harnackMu (harnackGridNodeBox h0 Q) < harnackMu (A ∩ harnackGridNodeBox h0 Q)

def harnackGridFirstDense {n : ℕ} (h0 q : ℝ) (A : Set (Point n)) (Q : harnackGridIndex n) : Prop :=
  0 < Q.1 ∧ harnackGridDense h0 q A Q ∧
    ∀ R : harnackGridIndex n, harnackGridDense h0 q A R →
      harnackGridNodeBox h0 Q ⊆ harnackGridNodeBox h0 R → Q.1 ≤ R.1

def harnackGridParentCandidate {n : ℕ} (h0 q : ℝ) (A : Set (Point n)) (P : harnackGridIndex n) : Prop :=
  ∃ Q : harnackGridIndex n, harnackGridFirstDense h0 q A Q ∧ harnackGridParent Q=P

def harnackGridSelectedParent {n : ℕ} (h0 q : ℝ) (A : Set (Point n)) (P : harnackGridIndex n) : Prop :=
  harnackGridParentCandidate h0 q A P ∧
    ∀ R : harnackGridIndex n, harnackGridParentCandidate h0 q A R →
      harnackGridNodeBox h0 P ⊆ harnackGridNodeBox h0 R → P.1 ≤ R.1

theorem harnack_first_dense_exists_at_point {n : ℕ} {h0 q : ℝ} {A : Set (Point n)} {p : Point n}
    (hDense : ∃ Q : harnackGridIndex n, p∈harnackGridNodeBox h0 Q ∧ harnackGridDense h0 q A Q)
    (hNoRoot : ∀ Q : harnackGridIndex n, Q.1=0 → p∈harnackGridNodeBox h0 Q →
      ¬harnackGridDense h0 q A Q) :
    ∃ Q : harnackGridIndex n, p∈harnackGridNodeBox h0 Q ∧ harnackGridFirstDense h0 q A Q := by
  classical
  have hExists : ∃ k : ℕ, ∃ Q : harnackGridIndex n,
      Q.1=k ∧ p∈harnackGridNodeBox h0 Q ∧ harnackGridDense h0 q A Q := by
    obtain ⟨Q,hpQ,hQ⟩ := hDense
    exact ⟨Q.1,Q,rfl,hpQ,hQ⟩
  obtain ⟨Q,hLevel,hpQ,hQ⟩ := Nat.find_spec hExists
  have hPositive : 0 < Q.1 := by
    by_contra h
    exact hNoRoot Q (by omega) hpQ hQ
  refine ⟨Q,hpQ,hPositive,hQ,?_⟩
  intro R hR hSub
  by_contra h
  have hMin := Nat.find_min hExists (show R.1 < Nat.find hExists by omega)
  exact hMin ⟨R,rfl,hSub hpQ,hR⟩

theorem harnack_first_dense_parent_not_dense {n : ℕ} {h0 q : ℝ} {A : Set (Point n)}
    {Q : harnackGridIndex n} (hQ : harnackGridFirstDense h0 q A Q)
    (hSub : harnackGridNodeBox h0 Q ⊆ harnackGridNodeBox h0 (harnackGridParent Q)) :
    ¬harnackGridDense h0 q A (harnackGridParent Q) := by
  intro hDenseParent
  have hLevel := hQ.2.2 (harnackGridParent Q) hDenseParent hSub
  change Q.1 ≤ Q.1-1 at hLevel
  have hPos := hQ.1
  omega

theorem harnack_selected_parent_above {n : ℕ} {h0 q : ℝ} {A : Set (Point n)}
    {P : harnackGridIndex n} (hP : harnackGridParentCandidate h0 q A P) :
    ∃ R : harnackGridIndex n, harnackGridSelectedParent h0 q A R ∧
      harnackGridNodeBox h0 P ⊆ harnackGridNodeBox h0 R := by
  classical
  have hExists : ∃ k : ℕ, ∃ R : harnackGridIndex n,
      R.1=k ∧ harnackGridParentCandidate h0 q A R ∧
        harnackGridNodeBox h0 P ⊆ harnackGridNodeBox h0 R := ⟨P.1,P,rfl,hP,Subset.rfl⟩
  obtain ⟨R,hLevel,hR,hPR⟩ := Nat.find_spec hExists
  refine ⟨R,⟨hR,?_⟩,hPR⟩
  intro S hS hRS
  by_contra h
  have hMin := Nat.find_min hExists (show S.1 < Nat.find hExists by omega)
  exact hMin ⟨S,rfl,hS,hPR.trans hRS⟩

theorem harnack_selected_parent_cover {n : ℕ} {h0 q : ℝ} {A : Set (Point n)}
    (hFirstCover : ∀ p∈A, ∃ Q : harnackGridIndex n,
      p∈harnackGridNodeBox h0 Q ∧ harnackGridFirstDense h0 q A Q)
    (hParentContain : ∀ Q : harnackGridIndex n, 0 < Q.1 →
      harnackGridNodeBox h0 Q ⊆ harnackGridNodeBox h0 (harnackGridParent Q)) :
    A ⊆ ⋃ P : {P : harnackGridIndex n // harnackGridSelectedParent h0 q A P}, harnackGridNodeBox h0 P.val := by
  intro p hp
  obtain ⟨Q,hpQ,hQ⟩ := hFirstCover p hp
  have hCand : harnackGridParentCandidate h0 q A (harnackGridParent Q) := ⟨Q,hQ,rfl⟩
  obtain ⟨P,hP,hParentSub⟩ := harnack_selected_parent_above hCand
  exact mem_iUnion.mpr ⟨⟨P,hP⟩,hParentSub (hParentContain Q hQ.1 hpQ)⟩

theorem harnack_selected_parent_disjoint_of_nesting {n : ℕ} {h0 q : ℝ} {A : Set (Point n)}
    (hSame : ∀ Q R : harnackGridIndex n, Q.1=R.1 → Q≠R →
      Disjoint (harnackGridNodeBox h0 Q) (harnackGridNodeBox h0 R))
    (hNest : ∀ Q R : harnackGridIndex n, Q.1 ≤ R.1 →
      (harnackGridNodeBox h0 Q ∩ harnackGridNodeBox h0 R).Nonempty →
      harnackGridNodeBox h0 R ⊆ harnackGridNodeBox h0 Q) :
    Pairwise (fun Q R : {Q : harnackGridIndex n // harnackGridSelectedParent h0 q A Q} =>
      Disjoint (harnackGridNodeBox h0 Q.val) (harnackGridNodeBox h0 R.val)) := by
  intro Q R hQR
  rw [disjoint_left]
  intro p hpQ hpR
  have hValues : Q.val≠R.val := fun h => hQR (Subtype.ext h)
  rcases lt_trichotomy Q.val.1 R.val.1 with h | h | h
  · have hSub := hNest Q.val R.val h.le ⟨p,hpQ,hpR⟩
    have hLevel := R.property.2 Q.val Q.property.1 hSub
    omega
  · exact (Set.disjoint_left.mp (hSame Q.val R.val h hValues)) hpQ hpR
  · have hSub := hNest R.val Q.val h.le ⟨p,hpR,hpQ⟩
    have hLevel := Q.property.2 R.val R.property.1 hSub
    omega


theorem harnack_grid_open_dense_at_point {n : ℕ} {h0 q : ℝ} (hh0 : 0 < h0) (hq : q < 1)
    {A : Set (Point n)} (hA : IsOpen A) {p : Point n} (hp : p∈A) :
    ∃ Q : harnackGridIndex n, p∈harnackGridNodeBox h0 Q ∧ harnackGridDense h0 q A Q := by
  obtain ⟨k,hk⟩ := harnack_grid_fine_subset_open_exists hh0 hA hp
  let Q := harnackGridContainingNode h0 k p
  refine ⟨Q,harnack_grid_containing_node_mem hh0 k p,?_⟩
  have hSub : harnackGridNodeBox h0 Q ⊆ A := hk k le_rfl
  have hEq : A ∩ harnackGridNodeBox h0 Q=harnackGridNodeBox h0 Q := inter_eq_right.mpr hSub
  have hPos : 0 < harnackMu (harnackGridNodeBox h0 Q) := by
    change 0 < harnackMu (harnackGridBox h0 Q.1 Q.2.1 Q.2.2)
    rw [harnack_grid_box_eq]
    exact harnack_box_mu_pos _ (harnack_grid_side_pos hh0 _) _
  unfold harnackGridDense
  rw [hEq]
  nlinarith

theorem harnack_grid_first_dense_cover {n : ℕ} {h0 q : ℝ} (hh0 : 0 < h0) (hq : q < 1)
    {A : Set (Point n)} (hA : IsOpen A)
    (hRoot : ∀ p∈A, ∀ Q : harnackGridIndex n, Q.1=0 → p∈harnackGridNodeBox h0 Q →
      ¬harnackGridDense h0 q A Q) :
    ∀ p∈A, ∃ Q : harnackGridIndex n, p∈harnackGridNodeBox h0 Q ∧ harnackGridFirstDense h0 q A Q := by
  intro p hp
  exact harnack_first_dense_exists_at_point (harnack_grid_open_dense_at_point hh0 hq hA hp) (hRoot p hp)

theorem harnack_grid_selected_parent_cover {n : ℕ} {h0 q : ℝ} (hh0 : 0 < h0) (hq : q < 1)
    {A : Set (Point n)} (hA : IsOpen A)
    (hRoot : ∀ p∈A, ∀ Q : harnackGridIndex n, Q.1=0 → p∈harnackGridNodeBox h0 Q →
      ¬harnackGridDense h0 q A Q) :
    A ⊆ ⋃ P : {P : harnackGridIndex n // harnackGridSelectedParent h0 q A P}, harnackGridNodeBox h0 P.val :=
  harnack_selected_parent_cover (harnack_grid_first_dense_cover hh0 hq hA hRoot)
    (harnack_grid_parent_contains hh0)

theorem harnack_grid_selected_parent_disjoint {n : ℕ} {h0 q : ℝ} (hh0 : 0 < h0)
    (A : Set (Point n)) :
    Pairwise (fun Q R : {Q : harnackGridIndex n // harnackGridSelectedParent h0 q A Q} =>
      Disjoint (harnackGridNodeBox h0 Q.val) (harnackGridNodeBox h0 R.val)) :=
  harnack_selected_parent_disjoint_of_nesting
    (harnack_grid_node_same_level_disjoint hh0) (harnack_grid_nested_of_levels_inter hh0)


theorem harnack_grid_selected_parent_transfer {n : ℕ} {h0 q m : ℝ}
    (hh0 : 0 < h0) (hq0 : 0 ≤ q) (hq1 : q < 1) (hm : 0 < m)
    {A B : Set (Point n)} (hA : IsOpen A)
    (hRoot : ∀ p∈A, ∀ Q : harnackGridIndex n, Q.1=0 → p∈harnackGridNodeBox h0 Q →
      ¬harnackGridDense h0 q A Q)
    (hForward : ∀ P : harnackGridIndex n, harnackGridSelectedParent h0 q A P →
      harnackGridCube h0 P.1 P.2.1 ×ˢ
        Ioc (harnackGridBottom h0 P.1 P.2.2+(harnackGridSide h0 P.1)^2)
          (harnackGridBottom h0 P.1 P.2.2+(harnackGridSide h0 P.1)^2+
            m*(harnackGridSide h0 P.1)^2) ⊆ B) :
    (volume : Measure (Point n)) A ≤ ENNReal.ofReal (q*(1+1/m))*(volume : Measure (Point n)) B := by
  classical
  let I := {P : harnackGridIndex n // harnackGridSelectedParent h0 q A P}
  let S : I → Set (Space n) := fun P => harnackGridCube h0 P.val.1 P.val.2.1
  let a : I → ℝ := fun P => harnackGridBottom h0 P.val.1 P.val.2.2
  let b : I → ℝ := fun P => a P+(harnackGridSide h0 P.val.1)^2
  have hBox (P : I) : S P ×ˢ Ioc (a P) (b P)=harnackGridNodeBox h0 P.val := rfl
  apply harnack_countable_parent_stack_measure_transfer hm hq0 S a b
    (fun P => harnack_grid_cube_measurable _ _ _) (fun P => by
      dsimp [b]; exact lt_add_of_pos_right _ (sq_pos_of_pos (harnack_grid_side_pos hh0 _))) hA.measurableSet
  · simpa only [hBox] using harnack_grid_selected_parent_disjoint hh0 A
  · simpa only [hBox] using harnack_grid_selected_parent_cover hh0 hq1 hA hRoot
  · intro P
    obtain ⟨Q,hQ,hQP⟩ := P.property.1
    have hND : ¬harnackGridDense h0 q A P.val := by
      rw [← hQP]
      exact harnack_first_dense_parent_not_dense hQ (harnack_grid_parent_contains hh0 Q hQ.1)
    have hReal : harnackMu (A ∩ harnackGridNodeBox h0 P.val) ≤
        q*harnackMu (harnackGridNodeBox h0 P.val) := le_of_not_gt hND
    have hFin : (volume : Measure (Point n)) (harnackGridNodeBox h0 P.val) ≠ ⊤ := by
      change (volume : Measure (Point n)) (harnackGridBox h0 P.val.1 P.val.2.1 P.val.2.2) ≠ ⊤
      rw [harnack_grid_box_eq]
      exact harnack_box_measure_ne_top _ (harnack_grid_side_pos hh0 _) _
    have hInterFin := ne_top_of_le_ne_top hFin (measure_mono (inter_subset_right (s := A)))
    have hCast := ENNReal.ofReal_le_ofReal hReal
    rw [ENNReal.ofReal_mul hq0] at hCast
    simpa only [harnackMu,ENNReal.ofReal_toReal hInterFin,ENNReal.ofReal_toReal hFin,hBox] using hCast
  · intro y hy
    obtain ⟨P,hP⟩ := mem_iUnion.mp hy
    apply hForward P.val P.property
    simpa only [S,a,b,add_sub_cancel_left] using hP

end Yau.LeafProofs.L05Aux
