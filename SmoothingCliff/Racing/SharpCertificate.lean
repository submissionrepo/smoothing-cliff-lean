import SmoothingCliff.Racing.Spread
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Sharp window certificates

This file formalizes the telescoping argument behind Proposition
`prop:sharpcertificate`.  For a monotone allocation slice on an interval,
uniform bounds on an arbitrarily fine family of translated windows imply the
global Lipschitz bound with the same coefficient.
-/

namespace SmoothingCliff.Racing

/-- A fixed positive window length controls every longer interval up to one
extra window.  The extra term is the initial remainder in the floor
decomposition of `y-x`. -/
theorem monotone_window_telescope_le
    {I : Set ℝ} (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : MonotoneOn f I)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    {x y h : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hxy : x < y) (hh : 0 < h) (hhd : h < y - x)
    (hWindow : ∀ s, s ∈ I → s + h ∈ I →
      f (s + h) - f s ≤ epsilon * h) :
    f y - f x ≤ epsilon * (y - x + h) := by
  let d := y - x
  let q : ℕ := ⌊d / h⌋₊
  let rem := d - (q : ℝ) * h
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr hxy
  have hratio0 : 0 ≤ d / h := (div_pos hd hh).le
  have hqRatio : (q : ℝ) ≤ d / h := by
    dsimp [q]
    exact Nat.floor_le hratio0
  have hqh : (q : ℝ) * h ≤ d := (le_div_iff₀ hh).mp hqRatio
  have hratioLt : d / h < (q : ℝ) + 1 := by
    simpa [q] using (Nat.lt_floor_add_one (d / h))
  have hdLt : d < ((q : ℝ) + 1) * h := (div_lt_iff₀ hh).mp hratioLt
  have hrem0 : 0 ≤ rem := by dsimp [rem]; linarith
  have hremLt : rem < h := by dsimp [rem]; linarith
  have hyEq : y = x + rem + (q : ℝ) * h := by
    dsimp [d, rem]
    ring
  have hIcc : Set.Icc x y ⊆ I := hI.out hx hy
  have hxRem : x + rem ∈ I := by
    apply hIcc
    constructor
    · linarith
    · rw [hyEq]
      nlinarith
  have hxH : x + h ∈ I := by
    apply hIcc
    constructor
    · linarith
    · linarith
  have htel : ∀ m : ℕ, m ≤ q →
      f (x + rem + (m : ℝ) * h) - f (x + rem) ≤
        (m : ℝ) * epsilon * h := by
    intro m
    induction m with
    | zero =>
        intro hm
        norm_num
    | succ m ih =>
        intro hm
        have hmle : m ≤ q := le_trans (Nat.le_succ m) hm
        have hmCast : ((m + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast hm
        let z := x + rem + (m : ℝ) * h
        have hzEq : z + h = x + rem + ((m + 1 : ℕ) : ℝ) * h := by
          simp only [z, Nat.cast_add, Nat.cast_one]
          ring
        have hzLower : x ≤ z := by
          dsimp [z]
          have hm0 : 0 ≤ (m : ℝ) := by positivity
          nlinarith [mul_nonneg hm0 hh.le]
        have hzUpper : z ≤ y := by
          rw [hyEq]
          have hmCast' : (m : ℝ) ≤ (q : ℝ) := by
            exact_mod_cast hmle
          nlinarith [mul_le_mul_of_nonneg_right hmCast' hh.le]
        have hzhLower : x ≤ z + h := by linarith
        have hzhUpper : z + h ≤ y := by
          rw [hzEq, hyEq]
          nlinarith [mul_le_mul_of_nonneg_right hmCast hh.le]
        have hzI : z ∈ I := hIcc ⟨hzLower, hzUpper⟩
        have hzhI : z + h ∈ I := hIcc ⟨hzhLower, hzhUpper⟩
        have hstep := hWindow z hzI hzhI
        have hind := ih hmle
        calc
          f (x + rem + ((m + 1 : ℕ) : ℝ) * h) - f (x + rem) =
              (f (z + h) - f z) + (f z - f (x + rem)) := by
            rw [hzEq]
            ring
          _ ≤ epsilon * h + (m : ℝ) * epsilon * h := add_le_add hstep hind
          _ = ((m + 1 : ℕ) : ℝ) * epsilon * h := by
            push_cast
            ring
  have hqWindows : f y - f (x + rem) ≤ (q : ℝ) * epsilon * h := by
    have h := htel q le_rfl
    rwa [← hyEq] at h
  have hmonRem : f (x + rem) ≤ f (x + h) := by
    apply hf hxRem hxH
    linarith
  have hfirstWindow := hWindow x hx hxH
  have hremBound : f (x + rem) - f x ≤ epsilon * h := by linarith
  have hsum : f y - f x ≤ ((q : ℝ) + 1) * epsilon * h := by
    linarith
  have hlength : ((q : ℝ) + 1) * h ≤ d + h := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hlength hepsilon
  dsimp [d] at hscaled
  nlinarith

/-- The ordered endpoint inequality obtained from arbitrarily fine windows. -/
theorem monotone_sub_le_of_arbitrarily_small_windows
    {I H : Set ℝ} (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : MonotoneOn f I)
    (epsilon : NNReal)
    (hFine : ∀ eta : ℝ, 0 < eta →
      ∃ h : ℝ, h ∈ H ∧ 0 < h ∧ h < eta)
    (hWindow : ∀ h, h ∈ H → ∀ s, s ∈ I → s + h ∈ I →
      f (s + h) - f s ≤ (epsilon : ℝ) * h)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hxy : x < y) :
    f y - f x ≤ (epsilon : ℝ) * (y - x) := by
  by_contra hbound
  have hstrict : (epsilon : ℝ) * (y - x) < f y - f x :=
    lt_of_not_ge hbound
  let gap := f y - f x - (epsilon : ℝ) * (y - x)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hepsDen : 0 < (epsilon : ℝ) + 1 := by positivity
  let eta := min (y - x) (gap / ((epsilon : ℝ) + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (sub_pos.mpr hxy) (div_pos hgap hepsDen)
  obtain ⟨h, hhH, hh0, hhEta⟩ := hFine eta heta
  have hhD : h < y - x := hhEta.trans_le (min_le_left _ _)
  have hhGap : h < gap / ((epsilon : ℝ) + 1) :=
    hhEta.trans_le (min_le_right _ _)
  have hscaledGap : ((epsilon : ℝ) + 1) * h < gap :=
    by simpa [mul_comm] using (lt_div_iff₀ hepsDen).mp hhGap
  have htelescope := monotone_window_telescope_le hI f hf
    (epsilon : ℝ) epsilon.2 hx hy hxy hh0 hhD (hWindow h hhH)
  dsimp [gap] at hscaledGap
  nlinarith

/-- Arbitrarily fine translated-window bounds characterize the global
Lipschitz coefficient of a monotone slice on an interval. -/
theorem monotone_lipschitzOnWith_of_arbitrarily_small_windows
    {I H : Set ℝ} (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : MonotoneOn f I)
    (epsilon : NNReal)
    (hFine : ∀ eta : ℝ, 0 < eta →
      ∃ h : ℝ, h ∈ H ∧ 0 < h ∧ h < eta)
    (hWindow : ∀ h, h ∈ H → ∀ s, s ∈ I → s + h ∈ I →
      f (s + h) - f s ≤ (epsilon : ℝ) * h) :
    LipschitzOnWith epsilon f I := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  simp only [Real.norm_eq_abs]
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have hmono : f x ≤ f y := hf hx hy hxy.le
    have hbound := monotone_sub_le_of_arbitrarily_small_windows
      hI f hf epsilon hFine hWindow hx hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hxy.le)]
    linarith
  · subst y
    simp
  · have hmono : f y ≤ f x := hf hy hx hyx.le
    have hbound := monotone_sub_le_of_arbitrarily_small_windows
      hI f hf epsilon hFine hWindow hy hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hyx.le)]
    exact hbound

/-- Sharp certificate equivalence for a family of positive admissible window
lengths accumulating at zero. -/
theorem monotone_lipschitzOnWith_iff_window_bounds
    {I H : Set ℝ} (hI : I.OrdConnected)
    (f : ℝ → ℝ) (hf : MonotoneOn f I)
    (epsilon : NNReal)
    (hPositive : ∀ h, h ∈ H → 0 < h)
    (hFine : ∀ eta : ℝ, 0 < eta →
      ∃ h : ℝ, h ∈ H ∧ 0 < h ∧ h < eta) :
    LipschitzOnWith epsilon f I ↔
      ∀ h, h ∈ H → ∀ s, s ∈ I → s + h ∈ I →
        f (s + h) - f s ≤ (epsilon : ℝ) * h := by
  constructor
  · intro hLip h hhH s hs hsh
    have hh := hPositive h hhH
    have hmono : f s ≤ f (s + h) := hf hs hsh (by linarith)
    have hnorm := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hs hsh
    simp only [Real.norm_eq_abs] at hnorm
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)] at hnorm
    have hscore : |s - (s + h)| = h := by
      rw [show s - (s + h) = -h by ring, abs_neg, abs_of_pos hh]
    rw [hscore] at hnorm
    linarith
  · intro hWindow
    exact monotone_lipschitzOnWith_of_arbitrarily_small_windows
      hI f hf epsilon hFine hWindow

/-- Uniform Lipschitz certificates for an arbitrary family of allocation
slices, indexed for example by the bidder and opponents' profile. -/
def UniformLipschitzCoefficient
    {A : Type*} (I : Set ℝ) (f : A → ℝ → ℝ) (epsilon : NNReal) : Prop :=
  ∀ alpha, LipschitzOnWith epsilon (f alpha) I

/-- Uniform translated-window certificates for the same family of slices. -/
def UniformWindowCoefficient
    {A : Type*} (I H : Set ℝ) (f : A → ℝ → ℝ)
    (epsilon : NNReal) : Prop :=
  ∀ alpha h, h ∈ H → ∀ s, s ∈ I → s + h ∈ I →
    f alpha (s + h) - f alpha s ≤ (epsilon : ℝ) * h

/-- The two families have exactly the same admissible uniform coefficients.
Consequently their least coefficients, whenever expressed as an infimum, are
identical. -/
theorem uniformCertificateCoefficients_eq
    {A : Type*} {I H : Set ℝ} (hI : I.OrdConnected)
    (f : A → ℝ → ℝ) (hf : ∀ alpha, MonotoneOn (f alpha) I)
    (hPositive : ∀ h, h ∈ H → 0 < h)
    (hFine : ∀ eta : ℝ, 0 < eta →
      ∃ h : ℝ, h ∈ H ∧ 0 < h ∧ h < eta) :
    {epsilon : NNReal | UniformLipschitzCoefficient I f epsilon} =
      {epsilon : NNReal | UniformWindowCoefficient I H f epsilon} := by
  ext epsilon
  simp only [Set.mem_setOf_eq, UniformLipschitzCoefficient,
    UniformWindowCoefficient]
  constructor
  · intro hLip alpha
    exact (monotone_lipschitzOnWith_iff_window_bounds
      hI (f alpha) (hf alpha) epsilon hPositive hFine).mp (hLip alpha)
  · intro hWindow alpha
    exact (monotone_lipschitzOnWith_iff_window_bounds
      hI (f alpha) (hf alpha) epsilon hPositive hFine).mpr (hWindow alpha)

end SmoothingCliff.Racing
