import Yau.Proofs.P06HodgeRegularityNondivergence

/-! Explicit finite coefficients for the prolonged scalar-principal
system on (u, D_i u). Derivatives of q remain first-order couplings. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq ι] [DecidableEq α]

abbrev RegularityProlongIndex (α ι : Type*) := α × Option ι

def regularityProlongValue (v : ι → E) (U : E → α → ℝ)
    (z : E) (p : RegularityProlongIndex α ι) : ℝ :=
  match p.2 with
  | none => U z p.1
  | some i => regularityDirection (v i) (fun y => U y p.1) z

def regularityProlongE1 (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ)
    (r c : RegularityProlongIndex α ι) (i : ι) (z : E) : ℝ :=
  match r.2, c.2 with
  | none, none => e1 r.1 c.1 i z
  | none, some _ => 0
  | some _, none => 0
  | some ell, some j => (if j = ell then e1 r.1 c.1 i z else 0) -
      if r.1 = c.1 then regularityDirection (v ell) (q i j) z else 0

def regularityProlongE0 (v : ι → E)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (r c : RegularityProlongIndex α ι) (z : E) : ℝ :=
  match r.2, c.2 with
  | none, none => e0 r.1 c.1 z
  | none, some _ => 0
  | some ell, none => regularityDirection (v ell) (e0 r.1 c.1) z
  | some ell, some j => (if j = ell then e0 r.1 c.1 z else 0) +
      regularityDirection (v ell) (e1 r.1 c.1 j) z

theorem regularity_ite_zero_regular (p : Prop) [Decidable p] (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun z => if p then f z else 0) ∧
      HasCompactSupport (fun z => if p then f z else 0) := by
  by_cases hp : p
  · simpa only [hp, ite_true] using And.intro hf hcf
  · simp only [hp, ite_false]
    exact ⟨contDiff_const, HasCompactSupport.zero⟩

theorem regularityProlongE1_regular
    (v : ι → E) (q : ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (r c : RegularityProlongIndex α ι) (i : ι) :
    ContDiff ℝ ∞ (regularityProlongE1 v q e1 r c i) ∧
      HasCompactSupport (regularityProlongE1 v q e1 r c i) := by
  rcases r with ⟨r, sr⟩
  rcases c with ⟨c, sc⟩
  cases sr with
  | none =>
    cases sc with
    | none => exact ⟨he1 r c i, hce1 r c i⟩
    | some j => exact ⟨contDiff_const, HasCompactSupport.zero⟩
  | some ell =>
    cases sc with
    | none => exact ⟨contDiff_const, HasCompactSupport.zero⟩
    | some j =>
      have h1 := regularity_ite_zero_regular (j = ell) (e1 r c i) (he1 r c i) (hce1 r c i)
      have h2 := regularity_ite_zero_regular (r = c) (regularityDirection (v ell) (q i j))
        (regularityDirection_contDiff (hq i j) (v ell)) ((hcq i j).fderiv_apply ℝ (v ell))
      exact ⟨h1.1.sub h2.1, h1.2.sub h2.2⟩

theorem regularityProlongE0_regular
    (v : ι → E) (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    (r c : RegularityProlongIndex α ι) :
    ContDiff ℝ ∞ (regularityProlongE0 v e1 e0 r c) ∧
      HasCompactSupport (regularityProlongE0 v e1 e0 r c) := by
  rcases r with ⟨r, sr⟩
  rcases c with ⟨c, sc⟩
  cases sr with
  | none =>
    cases sc with
    | none => exact ⟨he0 r c, hce0 r c⟩
    | some j => exact ⟨contDiff_const, HasCompactSupport.zero⟩
  | some ell =>
    cases sc with
    | none => exact ⟨regularityDirection_contDiff (he0 r c) (v ell), (hce0 r c).fderiv_apply ℝ (v ell)⟩
    | some j =>
      have h1 := regularity_ite_zero_regular (j = ell) (e0 r c) (he0 r c) (hce0 r c)
      have h2 := regularityDirection_contDiff (he1 r c j) (v ell)
      exact ⟨h1.1.add h2, h1.2.add ((hce1 r c j).fderiv_apply ℝ (v ell))⟩

end Yau.NodeProofs.P06Aux
