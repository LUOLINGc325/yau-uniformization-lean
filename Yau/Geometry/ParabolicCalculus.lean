import Yau.Blueprint.ParabolicSpaces

/-! Computed Levi-Civita tensor derivatives and the real representation of the
complex Monge–Ampère chart equation. No estimate is asserted in this module. -/
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- Covariant rank-r tensor coefficients in a fixed actual manifold chart. -/
abbrev CovTensor (n r : ℕ) := (Fin r → RIdx n) → ℝ

/-- ∇A, with the new derivative index first. Every connection term is computed
from the metric's Levi-Civita Christoffel coefficients. -/
def covariantD (h : HermitianField M) (x : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n) : CovTensor n (r+1) :=
  fun v => rDeriv (fun w => A w (fun j => v j.succ)) z (v 0) -
    ∑ j : Fin r, ∑ b : RIdx n,
      christoffel h x z b (v 0) (v j.succ) * A z (Function.update (fun i => v i.succ) j b)

/-- Fully covariant Riemann curvature, with the convention of `paperRm`. -/
def rmTensor (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) : CovTensor n 4 :=
  fun v => ∑ l, realMetricFn h x z l (v 3) * riemannCoeff h x z (v 0) (v 1) (v 2) l

/-- The actual k-fold covariant derivative of Rm, of rank 4+k. -/
def rmJet (h : HermitianField M) (x : M.Carrier) :
    (k : ℕ) → ComplexVector n → CovTensor n (4+k)
  | 0 => rmTensor h x
  | k+1 => covariantD h x (rmJet h x k)

/-- Metric contraction in every covariant slot (not a coordinate sup norm). -/
def covTensorNormSq (G : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) : ℝ :=
  ∑ v : Fin r → RIdx n, ∑ w : Fin r → RIdx n,
    A v * A w * ∏ j : Fin r, G⁻¹ (v j) (w j)

def curvatureJetNorm (h : HermitianField M) (k : ℕ) (x : M.Carrier) : ℝ :=
  Real.sqrt (covTensorNormSq (realMetricFn h x (chartPt x x)) (rmJet h x k (chartPt x x)))

/-- Ricci of the real Levi-Civita metric, with the same curvature convention. -/
def realRicciCoeff (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (j k : RIdx n) : ℝ :=
  ∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b *
    (∑ l, realMetricFn h x z l b * riemannCoeff h x z a j k l)

/-- Local real Ricci-flow normalization ∂tg=-σ Ric_real. The factor σ is
explicit because this paper's complex flow uses a different time scale from
∂tg=-2 Ric_real. The complex/real bridge remains an internal obligation. -/
def LocalRealRicciFlow (h : ℝ → HermitianField M) (O : Set M.Carrier)
    (I : Set ℝ) (σ : ℝ) : Prop :=
  MetricFamilySmooth h I ∧ ∀ x ∈ O, ∀ t ∈ I, ∀ a b : RIdx n,
    HasDerivWithinAt (fun s => realMetricFn (h s) x (chartPt x x) a b)
      (-σ * realRicciCoeff (h t) x (chartPt x x) a b) I t

end Yau

namespace Yau.Parabolic

/-- Matrix of multiplication by i on the ordered real basis (e_a,i e_a). -/
def complexJ (n : ℕ) : Mat n := fun i j =>
  if i.1 = j.1 then if i.2 = 0 ∧ j.2 = 1 then -1
    else if i.2 = 1 ∧ j.2 = 0 then 1 else 0 else 0

/-- Standard real representation of a Hermitian matrix. `sym` is the canonical
projection and is the identity on these entries when H is Hermitian. -/
def iota (H : Matrix (Fin n) (Fin n) ℂ) : Sym n :=
  sym (fun i j => if i.2 = j.2 then (H i.1 j.1).re
    else if i.2 = 0 then -(H i.1 j.1).im else (H i.1 j.1).im)

/-- ι(∂∂bar U)=1/4(D²U+JᵀD²U J), in the standard complex chart.
Equality to `leviC` is recorded as a bridge target, not assumed here. -/
def complexHessianMap (B : Sym n) : Sym n :=
  sym ((1/4 : ℝ) • ((B : Mat n) + (complexJ n).transpose * (B : Mat n) * complexJ n))

def logDetReal (B : Sym n) : ℝ := (1/2 : ℝ) * Real.log (B : Mat n).det

def backgroundRicci (A : Space n → Matrix (Fin n) (Fin n) ℂ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℂ :=
  -Yau.leviC (fun y => Real.log (A y).det.re) x

/-- The Lipschitz-in-time extension S(x,t_+) actually used at flow:255. -/
def clampedBackground (A : Space n → Matrix (Fin n) (Fin n) ℂ) (p : Point n) : Sym n :=
  iota (A p.1 - ((max p.2 0 : ℝ) : ℂ) • backgroundRicci A p.1)

def backgroundSource (A : Space n → Matrix (Fin n) (Fin n) ℂ) (p : Point n) : ℝ :=
  -Real.log (A p.1).det.re

end Yau.Parabolic
