import Yau.Proofs.F05HolderCaps
import Yau.LeafProofs.L16WordSource

/-! Computed one-variable derivatives for the finite positive-time bootstrap.
Intermediate fields are differentiated in a tangent line or in time, without
asserting premature joint differentiability of their spatial Hessians. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def F05RelD (X : Set (Space n)) (v : Point n → V) (z : Point n) : Space n →L[ℝ] V :=
  fderivWithin ℝ (fun x => v (x,z.2)) X z.1

def F05RelDD (X : Set (Space n)) (v : Point n → ℝ) (z : Point n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  fderivWithin ℝ (fun x => F05RelD X v (x,z.2)) X z.1

def F05RelT (I : Set ℝ) (v : Point n → V) (z : Point n) : V :=
  derivWithin (fun t => v (z.1,t)) I z.2

def F05RelC2 (X : Set (Space n)) (I : Set ℝ) (v : Point n → ℝ) : Prop :=
  ContinuousOn v (X ×ˢ I) ∧ ContinuousOn (F05RelD X v) (X ×ˢ I) ∧
  ContinuousOn (F05RelDD X v) (X ×ˢ I) ∧ ContinuousOn (F05RelT I v) (X ×ˢ I) ∧
  (∀ t ∈ I, ContDiffOn ℝ 2 (fun x => v (x,t)) X) ∧
  ∀ z ∈ X ×ˢ I, DifferentiableWithinAt ℝ (fun t => v (z.1,t)) I z.2

def F05RelSchauder (α : ℝ) (X : Set (Space n)) (I : Set ℝ) (v : Point n → ℝ) (C : ℝ) : Prop :=
  F05RelC2 X I v ∧ HolderBound α (X ×ˢ I) (fun z => (v z,F05RelD X v z)) C ∧
    HolderBound α (X ×ˢ I) (F05RelDD X v) C ∧ HolderBound α (X ×ˢ I) (F05RelT I v) C

def F05PosSpace (ν : Option (RIdx n)) : Set (Space n) :=
  closure (F05FlatOpen ν) ∩ Metric.ball 0 2

def F05PosPatch (ν : Option (RIdx n)) (T : ℝ) : Set (Point n) :=
  F05PosSpace ν ×ˢ Ioc 0 T

def F05QB (ν : Option (RIdx n)) (r : ℝ) : Set (Point n) :=
  region ν r ×ˢ Icc (-(r^2)) 0

def F05LocalSchauder (α : ℝ) (ν : Option (RIdx n)) (T : ℝ) (v : Point n → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 2 → ∀ s : ℝ, 0 < s → s < T →
    ∃ C : ℝ, 0 < C ∧ F05RelSchauder α (region ν r) (Icc s T) v C

def F05LocalHolder (α : ℝ) (ν : Option (RIdx n)) (T : ℝ) (v : Point n → V) : Prop :=
  ∀ r : ℝ, 0 < r → r < 2 → ∀ s : ℝ, 0 < s → s < T →
    ∃ C : ℝ, 0 < C ∧ HolderBound α (region ν r ×ˢ Icc s T) v C

def F05GoodPartial (T : ℝ) : Option (RIdx n) → (Point n → V) → Point n → V
  | none, f, z => derivWithin (fun t => f (z.1,t)) (Ioc 0 T) z.2
  | some j, f, z => deriv (fun a : ℝ => f (z.1+a • realVec j,z.2)) 0

def F05GoodWord (T : ℝ) : List (Option (RIdx n)) → (Point n → V) → Point n → V
  | [], f => f
  | a :: β, f => F05GoodPartial T a (F05GoodWord T β f)

def F05GoodLetter (ν a : Option (RIdx n)) : Prop :=
  match ν,a with
  | some j,some k => k ≠ j
  | _,_ => True

def F05GoodList (ν : Option (RIdx n)) (β : List (Option (RIdx n))) : Prop :=
  ∀ a ∈ β, F05GoodLetter ν a

def F05GoodDiffOn (T : ℝ) (a : Option (RIdx n)) (f : Point n → V) (Q : Set (Point n)) : Prop :=
  ∀ z ∈ Q, match a with
  | none => DifferentiableWithinAt ℝ (fun t => f (z.1,t)) (Ioc 0 T) z.2
  | some j => DifferentiableAt ℝ (fun s : ℝ => f (z.1+s • realVec j,z.2)) 0

def F05ZeroFace (ν : Option (RIdx n)) (T : ℝ) (v : Point n → V) : Prop :=
  match ν with
  | none => True
  | some j => ∀ x ∈ Metric.ball 0 2, realCoord x j = 0 → ∀ t ∈ Ioc 0 T, v (x,t) = 0

def F05RelOp (X : Set (Space n)) (I : Set ℝ) (a : Point n → Mat n)
    (b : Point n → RIdx n → ℝ) (v : Point n → ℝ) (z : Point n) : ℝ :=
  F05RelT I v z-(∑ j,∑ k,a z j k*F05RelDD X v z (realVec j) (realVec k))-
    ∑ j,b z j*F05RelD X v z (realVec j)

def F05GoodCorrection (T : ℝ) (X : Set (Space n)) (a : Point n → Mat n)
    (b : Point n → RIdx n → ℝ) (u : Point n → ℝ)
    (s t : List (Option (RIdx n))) (z : Point n) : ℝ :=
  (∑ j,∑ k,F05GoodWord T s a z j k*F05RelDD X (F05GoodWord T t u) z (realVec j) (realVec k))+
    ∑ j,F05GoodWord T s (fun p => b p j) z*F05RelD X (F05GoodWord T t u) z (realVec j)

def F05GoodSource (T : ℝ) (X : Set (Space n)) (a : Point n → Mat n)
    (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ)
    (β : List (Option (RIdx n))) (z : Point n) : ℝ :=
  F05GoodWord T β f z+
    ((commutatorSplits β).map (fun st => F05GoodCorrection T X a b u st.1 st.2 z)).sum

end Yau.Proofs.F05Aux
