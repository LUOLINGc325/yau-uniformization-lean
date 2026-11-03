import Yau.LeafProofs.L05PositiveMatrices

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def tracePair {n : ℕ} (A B : Sym n) : ℝ := Matrix.trace ((A : Mat n)*(B : Mat n))

def slopeSet (n : ℕ) (ell L : ℝ) : Set (Sym n) :=
  {A | ((A : Mat n)-ell • (1 : Mat n)).PosSemidef ∧
    (L • (1 : Mat n)-(A : Mat n)).PosSemidef}

theorem slopeSet_nonempty (n : ℕ) {ell L : ℝ} (h : ell ≤ L) :
    (slopeSet n ell L).Nonempty := by
  let A : Sym n := ⟨ell • (1 : Mat n),
    IsSelfAdjoint.smul (IsSelfAdjoint.all _) (IsSelfAdjoint.one _)⟩
  refine ⟨A,?_,?_⟩
  · change ((ell • (1 : Mat n))-(ell • (1 : Mat n))).PosSemidef
    simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : Mat n).PosSemidef)
  · change (L • (1 : Mat n)-ell • (1 : Mat n)).PosSemidef
    rw [← sub_smul]
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr h)

theorem slopeSet_posSemidef {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell)
    {A : Sym n} (hA : A ∈ slopeSet n ell L) : (A : Mat n).PosSemidef := by
  have hh := hA.1.add (Matrix.PosSemidef.one.smul hell :
    (ell • (1 : Mat n)).PosSemidef)
  simpa only [sub_add_cancel] using hh

theorem slopeSet_norm_le {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell)
    {A : Sym n} (hA : A ∈ slopeSet n ell L) : ‖A‖ ≤ (2*n)*L := by
  have ht : Matrix.trace (A : Mat n) ≤ (Fintype.card (RIdx n) : ℝ)*L := by
    calc
      _ = ∑ i, (A : Mat n) i i := rfl
      _ ≤ ∑ _i : RIdx n, L := Finset.sum_le_sum fun i _ => by
        have hd := hA.2.diag_nonneg (i := i)
        simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
          sub_nonneg] using hd
      _ = _ := by simp
  have hn := posSemidef_norm_le_trace (slopeSet_posSemidef hell hA)
  have hc : (Fintype.card (RIdx n) : ℝ) = 2*n := by simp [RIdx]; ring
  rw [hc] at ht
  exact hn.trans ht

theorem abs_trace_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    |Matrix.trace (A*B)| ≤ Real.sqrt (Fintype.card ι)*‖A‖*‖B‖ := by
  have hp := trace_le_sqrt_card_mul_norm (A*B)
  have hn := trace_le_sqrt_card_mul_norm (-(A*B))
  simp only [Matrix.trace_neg,norm_neg] at hn
  have hab : |Matrix.trace (A*B)| ≤ Real.sqrt (Fintype.card ι)*‖A*B‖ :=
    abs_le.mpr ⟨by linarith,hp⟩
  have hh := mul_le_mul_of_nonneg_left (Matrix.frobenius_norm_mul A B)
    (Real.sqrt_nonneg (Fintype.card ι))
  exact hab.trans (by simpa only [mul_assoc] using hh)

theorem tracePair_image_bddAbove {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell)
    (H : Sym n) : BddAbove {z | ∃ A ∈ slopeSet n ell L, z = tracePair A H} := by
  refine ⟨Real.sqrt (Fintype.card (RIdx n))*((2*n)*L)*‖H‖,?_⟩
  rintro z ⟨A,hA,rfl⟩
  calc
    _ ≤ |tracePair A H| := le_abs_self _
    _ ≤ Real.sqrt (Fintype.card (RIdx n))*‖A‖*‖H‖ := abs_trace_mul_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (slopeSet_norm_le hell hA) (Real.sqrt_nonneg _)) (norm_nonneg _)

def globalElliptic {n : ℕ} (F : Sym n → ℝ) (ell L : ℝ) : Prop :=
  ∀ N P : Sym n, (P : Mat n).PosSemidef →
    ell*Matrix.trace (P : Mat n) ≤ F (N+P)-F N ∧
    F (N+P)-F N ≤ L*Matrix.trace (P : Mat n)

/-- The total real supremum is only a definition here. Applications must
first establish that the slope set is nonempty and its image is bounded. -/
def pucciPlus {n : ℕ} (ell L : ℝ) (H : Sym n) : ℝ :=
  sSup {z | ∃ A ∈ slopeSet n ell L, z = tracePair A H}

theorem tracePair_image_nonempty {n : ℕ} {ell L : ℝ} (h : ell ≤ L) (H : Sym n) :
    ({z | ∃ A ∈ slopeSet n ell L, z = tracePair A H} : Set ℝ).Nonempty := by
  rcases slopeSet_nonempty n h with ⟨A,hA⟩
  exact ⟨tracePair A H,A,hA,rfl⟩

theorem tracePair_le_pucciPlus {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell)
    {A : Sym n} (hA : A ∈ slopeSet n ell L) (H : Sym n) :
    tracePair A H ≤ pucciPlus ell L H :=
  le_csSup (tracePair_image_bddAbove hell H) ⟨A,hA,rfl⟩

theorem pucciPlus_le {n : ℕ} {ell L z : ℝ} (h : ell ≤ L) (H : Sym n)
    (hz : ∀ A ∈ slopeSet n ell L, tracePair A H ≤ z) : pucciPlus ell L H ≤ z := by
  apply csSup_le (tracePair_image_nonempty h H)
  rintro y ⟨A,hA,rfl⟩
  exact hz A hA

theorem pucciPlus_zero {n : ℕ} {ell L : ℝ} (hell : 0 ≤ ell) (h : ell ≤ L) :
    pucciPlus (n := n) ell L 0 = 0 := by
  apply le_antisymm
  · exact pucciPlus_le h 0 (fun A _ => by simp [tracePair])
  · rcases slopeSet_nonempty n h with ⟨A,hA⟩
    simpa [tracePair] using tracePair_le_pucciPlus hell hA 0

def touchAbove {n : ℕ} (φ v : Point n → ℝ) (p : Point n) : Prop :=
  φ p = v p ∧ ∀ᶠ q in 𝓝 p, v q ≤ φ q

def touchBelow {n : ℕ} (φ v : Point n → ℝ) (p : Point n) : Prop :=
  φ p = v p ∧ ∀ᶠ q in 𝓝 p, φ q ≤ v q

def viscositySub {n : ℕ} (Q : Set (Point n)) (G : Sym n → Point n → ℝ)
    (f v : Point n → ℝ) : Prop :=
  ∀ p ∈ Q, ∀ φ : Point n → ℝ, ContDiffAt ℝ 2 φ p → touchAbove φ v p →
    timeD Set.univ φ p-G (hessian φ p) p ≤ f p

def viscositySuper {n : ℕ} (Q : Set (Point n)) (G : Sym n → Point n → ℝ)
    (f v : Point n → ℝ) : Prop :=
  ∀ p ∈ Q, ∀ φ : Point n → ℝ, ContDiffAt ℝ 2 φ p → touchBelow φ v p →
    f p ≤ timeD Set.univ φ p-G (hessian φ p) p

def viscositySolution {n : ℕ} (Q : Set (Point n)) (G : Sym n → Point n → ℝ)
    (f v : Point n → ℝ) : Prop := viscositySub Q G f v ∧ viscositySuper Q G f v

def unitClosed (n : ℕ) : Set (Point n) := cylinder (Metric.closedBall 0 1) (-1) 0

def unitOpen (n : ℕ) : Set (Point n) := Metric.ball 0 1 ×ˢ Set.Ioo (-1) 0

def parabolicBoundary (n : ℕ) : Set (Point n) :=
  (Metric.closedBall 0 1 ×ˢ ({-1} : Set ℝ)) ∪
    (Metric.sphere 0 1 ×ˢ Set.Icc (-1) 0)

/-- An unresolved lower contact/area theorem, with no regularity conclusion.
This proposition is a tracking boundary, and is not assumed by any endpoint. -/
def ParabolicContactABPGap : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∃ C : ℝ, 0 < C ∧ ∀ v g : Point n → ℝ,
      ContinuousOn v (unitClosed n) → ContinuousOn g (unitClosed n) →
      (∀ p ∈ parabolicBoundary n, v p ≤ 0) →
      viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) g v →
      ∀ p ∈ unitClosed n, v p ≤ C *
        (∫ z, (max (g z) 0)^(2*n+1)
          ∂productVolume (Metric.ball 0 1) (Set.Ioo (-1) 0))^
            (1/((2*n+1 : ℕ) : ℝ))

/-- The two actual viscosity jet rules required by finite differences.
There is no differentiability or Hölder conclusion in this lower boundary. -/
def ParabolicJetCombinationGap : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∀ (Q : Set (Point n)) (F : Sym n → ℝ), IsOpen Q → Continuous F →
      globalElliptic F ell L →
      (∀ u v : Point n → ℝ, ContinuousOn u Q → ContinuousOn v Q →
        viscositySub Q (fun H _ => F H) (fun _ => 0) u →
        viscositySuper Q (fun H _ => F H) (fun _ => 0) v →
        viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) (u-v)) ∧
      (ConcaveOn ℝ Set.univ F → ∀ u v : Point n → ℝ,
        ContinuousOn u Q → ContinuousOn v Q →
        viscositySub Q (fun H _ => F H) (fun _ => 0) u →
        viscositySub Q (fun H _ => F H) (fun _ => 0) v →
        ∀ θ : ℝ, θ ∈ Set.Icc 0 1 →
        viscositySub Q (fun H _ => F H) (fun _ => 0)
          (fun p => θ*u p+(1-θ)*v p))

/-- Continuous autonomous Dirichlet existence, without any jet estimate. -/
def FrozenBellmanDirichletGap : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
      ConcaveOn ℝ Set.univ F → F 0 = 0 →
      ∀ (g : Point n → ℝ) (B : ℝ), 0 ≤ B → ContinuousOn g (unitClosed n) →
        (∀ p ∈ unitClosed n, |g p| ≤ B) →
        ∃ v : Point n → ℝ, ContinuousOn v (unitClosed n) ∧
          Set.EqOn v g (parabolicBoundary n) ∧
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) v ∧
          ∀ p ∈ unitClosed n, |v p| ≤ B

end Yau.LeafProofs.L05Aux
